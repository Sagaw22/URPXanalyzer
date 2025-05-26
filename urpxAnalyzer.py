#!/usr/bin/env python3
"""
urscript_analyzer.py

Static-analysis toolkit for URScript.

* CLI or PyQt5 GUI (run with no arguments)
* Batch-processing of .script files / folders
* Metrics per file **and per function**:
    • size & structure (LOC, comments, blanks, duplication)
    • complexity (McCabe, nesting, conditional breakdown)
    • deep-dive (Halstead, MI, fan-in/out …)
    • Optimove (optimoveJ/L) & safety call counts
"""

from __future__ import annotations
import sys, os, re, argparse, json, csv
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Optional
from collections import Counter
from math import log2
from pathlib import Path

# ---------------------------------------------------------------------------
# Domain keywords
# ---------------------------------------------------------------------------
MOVE_CMDS = ("optimovej", "optimovel", "movej", "movel")  # ← only these wrappers are counted

SAFETY_FUNCS = (
    "protective_stop", "set_safety_mode", "stopl", "stopj",
    "freedrive_mode", "end_freedrive_mode", "power_off",
    "power_on", "brake_release",
)

MOVE_RE   = re.compile(r'\b(?:' + '|'.join(map(re.escape, MOVE_CMDS)) + r')\b', re.IGNORECASE)
SAFETY_RE = re.compile(r'\b(?:' + '|'.join(map(re.escape, SAFETY_FUNCS)) + r')\b', re.IGNORECASE)

CONDITIONAL_KEYWORDS = ("if", "elif", "while", "for", "and", "or")
COND_SET = set(CONDITIONAL_KEYWORDS)
COMMENT_RE = re.compile(r"\s*#")

# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------
@dataclass
class FunctionInfo:
    name: str
    start: int
    end: int
    loc: int = 0
    cloc: int = 0
    blank: int = 0
    mccabe: int = 1
    conditionals: Counter = field(default_factory=Counter)
    max_depth: int = 0
    move_cmds: int = 0               # optimoveJ/L only
    safety_calls: int = 0
    operators: Counter = field(default_factory=Counter)
    operands: Counter = field(default_factory=Counter)
    params: int = 0
    returns: int = 0
    fan_in: int = 0
    fan_out: int = 0
    longest_stmt: int = 0
    halstead: Dict[str, float] = field(default_factory=dict)
    maintainability_index: float = 0.0

    @property
    def comment_percent(self) -> float:
        return 100.0 * self.cloc / self.loc if self.loc else 0.0

    def to_json(self) -> dict:
        d = asdict(self)
        d["comment_percent"] = self.comment_percent
        return d


@dataclass
class FileReport:
    path: str
    loc: int = 0
    cloc: int = 0
    blank: int = 0
    mccabe: int = 0
    relative_mccabe: float = 0.0
    duplicate_ratio: float = 0.0
    move_cmds: int = 0               # optimoveJ/L only
    safety_calls: int = 0
    conditional_counts: Counter = field(default_factory=Counter)
    functions: List[FunctionInfo] = field(default_factory=list)

    def to_json(self) -> dict:
        d = asdict(self)
        d["conditional_counts"] = dict(self.conditional_counts)
        d["functions"] = [f.to_json() for f in self.functions]
        return d


# ---------------------------------------------------------------------------
# Analyzer
# ---------------------------------------------------------------------------
class URScriptAnalyzer:
    def __init__(self, filepath: str | os.PathLike):
        self.filepath = str(filepath)
        with open(filepath, "r", encoding="utf-8") as f:
            self.lines = f.readlines()
        self.report = FileReport(path=self.filepath)

    # ---------------- main entry ----------------
    def analyze(self, func_filter: Optional[set[str]] = None):
        self._scan_lines()
        self._extract_functions(func_filter)
        self._duplication()
        self._aggregate()

    # ---------------- top-level scan ----------------
    def _scan_lines(self):
        for line in self.lines:
            stripped = line.rstrip("\n")
            if COMMENT_RE.match(stripped):
                self.report.cloc += 1
            elif not stripped.strip():
                self.report.blank += 1
            else:
                self.report.loc += 1

            if MOVE_RE.search(stripped):
                self.report.move_cmds += 1
            if SAFETY_RE.search(stripped):
                self.report.safety_calls += 1

    # ---------------- functions & complexity ----------------
    def _extract_functions(self, func_filter: Optional[set[str]]):
        stack: List[FunctionInfo] = []
        indent_stack: List[int] = []

        def flush(idx: int):
            if not stack:
                return
            fi = stack.pop()
            fi.end = idx
            fi.loc = fi.end - fi.start + 1
            for l in self.lines[fi.start - 1 : fi.end]:
                s = l.strip()
                if COMMENT_RE.match(s):
                    fi.cloc += 1
                elif not s:
                    fi.blank += 1
            if func_filter is None or fi.name in func_filter:
                self._deep_metrics(fi)
            self.report.functions.append(fi)

        for idx, raw in enumerate(self.lines, 1):
            stripped = raw.rstrip("\n")
            indent = len(raw) - len(raw.lstrip(" "))

            # function start?
            m = re.match(r"^(def|sec|thread)\s+(\w+)\s*\(", stripped.lstrip())
            if m:
                stack.append(FunctionInfo(name=m.group(2), start=idx, end=idx))
                indent_stack.append(indent)
                continue

            # dedent → close functions
            while indent_stack and indent < indent_stack[-1]:
                indent_stack.pop()
                flush(idx - 1)

            if not stack:
                continue

            fi = stack[-1]

            if MOVE_RE.search(stripped):
                fi.move_cmds += 1
            if SAFETY_RE.search(stripped):
                fi.safety_calls += 1

            depth = self._indent_depth(raw)
            fi.max_depth = max(fi.max_depth, depth)

            tokens = re.findall(r'\b\w+\b', stripped.lower())
            for tok in tokens:
                if tok in COND_SET and tok in ("if", "elif", "while", "for"):
                    fi.mccabe += 1
                    self.report.conditional_counts[tok] += 1
                    fi.conditionals[tok] += 1

                if tok in COND_SET or tok in MOVE_CMDS:
                    fi.operators[tok] += 1
                elif tok.isdigit():
                    fi.operands[tok] += 1
                elif tok.isidentifier():
                    (fi.operators if tok.islower() else fi.operands)[tok] += 1

            fi.longest_stmt = max(fi.longest_stmt, len(stripped))

        flush(len(self.lines))

        # fan-in / fan-out
        name_map = {f.name: f for f in self.report.functions}
        call_re = re.compile(r"\b([A-Za-z_]\w*)\s*\(")
        for f in self.report.functions:
            body = "\n".join(self.lines[f.start - 1 : f.end])
            refs = call_re.findall(body)
            f.fan_out = len(refs)
            for r in refs:
                if r in name_map and r != f.name:
                    name_map[r].fan_in += 1

    # ---------------- deep metrics ----------------
    def _deep_metrics(self, fi: FunctionInfo):
        header = self.lines[fi.start - 1].strip()
        params = header[header.find("(")+1 : header.find(")")] if "(" in header else ""
        fi.params = 0 if not params.strip() else params.count(",") + 1
        fi.returns = sum(1 for l in self.lines[fi.start : fi.end] if re.search(r"\breturn\b", l))

        n1, n2 = len(fi.operators), len(fi.operands)
        N1, N2 = sum(fi.operators.values()), sum(fi.operands.values())
        vocab, length = n1 + n2, N1 + N2
        if vocab and length:
            volume = length * log2(max(vocab, 2))
            difficulty = (n1 / 2) * (N2 / max(n2, 1))
            effort = volume * difficulty
        else:
            volume = difficulty = effort = 0.0
        fi.halstead = {"volume": volume, "difficulty": difficulty, "effort": effort}

        fi.maintainability_index = max(
            0.0,
            171
            - 5.2 * (log2(volume) if volume else 0)
            - 0.23 * fi.mccabe
            - 16.2 * (log2(fi.loc) if fi.loc else 0),
        )

    # ---------------- duplication ----------------
    def _duplication(self):
        code = [re.sub(r"\s+", "", l) for l in self.lines if l.strip() and not COMMENT_RE.match(l)]
        if code:
            self.report.duplicate_ratio = 1 - len(set(code)) / len(code)

    # ---------------- aggregate ----------------
    def _aggregate(self):
        if self.report.functions:
            self.report.mccabe = sum(f.mccabe for f in self.report.functions)
            self.report.relative_mccabe = self.report.mccabe / len(self.report.functions)

    @staticmethod
    def _indent_depth(raw: str, size: int = 2) -> int:
        return (len(raw) - len(raw.lstrip(" "))) // size


# ---------------------------------------------------------------------------
# CLI helpers
# ---------------------------------------------------------------------------
def gather(paths: List[str], recursive: bool) -> List[str]:
    out = []
    for p in paths:
        pth = Path(p)
        if pth.is_dir():
            pattern = "**/*.script" if recursive else "*.script"
            out.extend(map(str, pth.glob(pattern)))
        elif pth.is_file():
            out.append(str(pth))
    return sorted(set(out))


def run_cli(args):
    files = gather(args.paths, args.recursive)
    if not files:
        print("No .script files found.", file=sys.stderr)
        sys.exit(1)

    reports = []
    for fp in files:
        a = URScriptAnalyzer(fp)
        a.analyze(set(args.functions) if args.functions else None)
        reports.append(a.report)

    if args.format == "json":
        json.dump([r.to_json() for r in reports], sys.stdout, indent=2)
    else:
        fld = [
            "path", "loc", "cloc", "blank",
            "mccabe", "relative_mccabe", "duplicate_ratio",
            "move_cmds", "safety_calls",
        ]
        w = csv.DictWriter(sys.stdout, fieldnames=fld); w.writeheader()
        for r in reports:
            w.writerow({k: getattr(r, k) for k in fld})


# ---------------------------------------------------------------------------
# GUI ---------------------------------------------------------------
# ---------------------------------------------------------------------------
def run_gui():
    from PyQt5.QtWidgets import (
        QApplication, QMainWindow, QFileDialog, QTabWidget, QWidget, QVBoxLayout,
        QPushButton, QTableWidget, QTableWidgetItem, QHBoxLayout, QTreeWidget,
        QTreeWidgetItem, QMessageBox, QLabel, QHeaderView
    )
    from PyQt5.QtCore import Qt

    class Main(QMainWindow):
        def __init__(self):
            super().__init__()
            self.setWindowTitle("URScript Analyzer")
            self.resize(1000, 700)
            self.tabs = QTabWidget(); self.setCentralWidget(self.tabs)
            self.files: List[str] = []; self.reports: List[FileReport] = []
            self._batch_tab(); self._results_tab(); self._func_tab()

        # ---------------- batch tab ----------------
        def _batch_tab(self):
            w = QWidget(); v = QVBoxLayout(w)
            h = QHBoxLayout()
            b_files, b_dir, b_run = QPushButton("Add files"), QPushButton("Add folder"), QPushButton("Analyze")
            h.addWidget(b_files); h.addWidget(b_dir); h.addStretch(); h.addWidget(b_run)
            v.addLayout(h)
            self.info = QLabel("No files selected."); v.addWidget(self.info)
            b_files.clicked.connect(self._add_files)
            b_dir.clicked.connect(self._add_dir)
            b_run.clicked.connect(self._run)
            self.tabs.addTab(w, "Batch")

        def _add_files(self):
            f, _ = QFileDialog.getOpenFileNames(self, "Select .script", "", "URScript (*.script)")
            if f: self.files.extend(f); self._update_info()

        def _add_dir(self):
            d = QFileDialog.getExistingDirectory(self, "Select folder", "", QFileDialog.ShowDirsOnly)
            if d:
                self.files.extend(str(p) for p in Path(d).rglob("*.script"))
                self._update_info()

        def _update_info(self):
            self.files = sorted(set(self.files))
            self.info.setText(f"{len(self.files)} file(s) ready")

        def _run(self):
            if not self.files:
                QMessageBox.warning(self, "No files", "Add files first"); return
            self.reports = []
            for f in self.files:
                a = URScriptAnalyzer(f); a.analyze()
                self.reports.append(a.report)
            QMessageBox.information(self, "Done", f"Analyzed {len(self.reports)} file(s)")
            self._fill_results(); self._fill_tree()

        # ---------------- results tab ----------------
        def _results_tab(self):
            self.res = QTableWidget(); self.res.setColumnCount(9)
            self.res.setHorizontalHeaderLabels([
                "File", "LOC", "Comment", "Blank",
                "McCabe", "Rel.McCabe", "Dup %",
                "Optimove", "Safety"
            ])
            self.res.horizontalHeader().setSectionResizeMode(0, QHeaderView.Stretch)
            self.res.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeToContents)
            self.tabs.addTab(self.res, "Results")

        def _fill_results(self):
            self.res.setRowCount(len(self.reports))
            for r, rep in enumerate(self.reports):
                vals = [
                    os.path.basename(rep.path), rep.loc, rep.cloc, rep.blank,
                    rep.mccabe, f"{rep.relative_mccabe:.2f}",
                    f"{rep.duplicate_ratio:.2%}", rep.move_cmds, rep.safety_calls
                ]
                for c, v in enumerate(vals):
                    itm = QTableWidgetItem(str(v))
                    itm.setTextAlignment(Qt.AlignCenter if c else Qt.AlignLeft)
                    self.res.setItem(r, c, itm)
            self.res.resizeRowsToContents()

        # ---------------- function explorer ----------------
        def _func_tab(self):
            w = QWidget(); h = QHBoxLayout(w)
            self.tree = QTreeWidget(); self.tree.setHeaderLabel("Functions")
            h.addWidget(self.tree, 2)
            self.tbl = QTableWidget()
            cols = [
                "File", "Func", "LOC", "McCabe", "Depth",
                "Params", "Returns", "Fan-in", "Fan-out",
                "Optimove", "Safety", "Halstead V", "MI", "Comment %"
            ]
            self.tbl.setColumnCount(len(cols)); self.tbl.setHorizontalHeaderLabels(cols)
            self.tbl.horizontalHeader().setSectionResizeMode(0, QHeaderView.Stretch)
            self.tbl.horizontalHeader().setSectionResizeMode(1, QHeaderView.Stretch)
            h.addWidget(self.tbl, 5)
            btn = QPushButton("Re-analyse selection"); btn.clicked.connect(self._reanalyze)
            h.addWidget(btn, 0)
            self.tabs.addTab(w, "Functions")

        def _fill_tree(self):
            self.tree.clear()
            for rep in self.reports:
                top = QTreeWidgetItem([os.path.basename(rep.path)])
                top.setFlags(top.flags() | Qt.ItemIsTristate | Qt.ItemIsUserCheckable)
                self.tree.addTopLevelItem(top)
                for f in rep.functions:
                    child = QTreeWidgetItem([f.name]); child.setCheckState(0, Qt.Unchecked)
                    top.addChild(child)

        def _reanalyze(self):
            wanted = {child.text(0)
                      for i in range(self.tree.topLevelItemCount())
                      for child in self._iter(self.tree.topLevelItem(i))
                      if child.checkState(0) == Qt.Checked}
            if not wanted:
                QMessageBox.warning(self, "None", "Select functions"); return
            rows = []
            for rep in self.reports:
                a = URScriptAnalyzer(rep.path); a.analyze(wanted)
                for f in a.report.functions:
                    if f.name in wanted:
                        rows.append([
                            os.path.basename(rep.path), f.name, f.loc, f.mccabe, f.max_depth,
                            f.params, f.returns, f.fan_in, f.fan_out,
                            f.move_cmds, f.safety_calls,
                            f.halstead.get("volume", 0.0),
                            f"{f.maintainability_index:.1f}", f"{f.comment_percent:.1f}%"
                        ])
            self.tbl.setRowCount(len(rows))
            for r, row in enumerate(rows):
                for c, v in enumerate(row):
                    itm = QTableWidgetItem(str(v))
                    itm.setTextAlignment(Qt.AlignCenter if c > 1 else Qt.AlignLeft)
                    self.tbl.setItem(r, c, itm)
            self.tbl.resizeColumnsToContents(); self.tbl.resizeRowsToContents()

        @staticmethod
        def _iter(item):
            for i in range(item.childCount()):
                yield item.child(i)

    # ----- QApplication & event loop (GC-safe) -----
    app = QApplication(sys.argv)
    window = Main()      # keep a ref so it’s not GC’d
    window.show()
    app.exec_()


# ---------------------------------------------------------------------------
# entry point
# ---------------------------------------------------------------------------
def main():
    p = argparse.ArgumentParser(description="Static analyzer for URScript (optimove counter).")
    p.add_argument("paths", nargs="*", help="Files or folders to analyze")
    p.add_argument("-r", "--recursive", action="store_true", help="Recurse into sub-folders")
    p.add_argument("--functions", "-fn", nargs="+", help="Deep-metrics only for these functions")
    p.add_argument("-f", "--format", choices=("json", "csv"), default="json", help="CLI output format")
    args = p.parse_args()
    if not args.paths:
        run_gui()
    else:
        run_cli(args)


if __name__ == "__main__":
    main()