#!/usr/bin/env python3
"""
convert.py — Convert sparse graph matrices to adjacency lists.

Supported input:
  - Harwell–Boeing assembled sparse matrices (e.g. .rua, .rsa, .hb, extensionless)
  - Matrix Market coordinate matrices (.mtx)

Output format (1-based vertex labels):
  # vertices: N
  # edges: M
  # mode: undirected
  1: 2, 5
  2: 1
  ...

Examples:
  python convert.py arc130.rua
  python convert.py data/arc130 --out output/arc130_adj.txt
  python convert.py data --batch --out-dir adjacency
  python convert.py data --batch --recursive --mode undirected --out-dir adjacency
  python convert.py graph.mtx --mode directed
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Iterable


def _fortran_format_width(fmt: str) -> int:
    """Get field width from common Fortran formats, e.g. (16I5), (3E24.16)."""
    m = re.search(r"\d*[A-Za-z](\d+)(?:\.\d+)?", fmt.replace(" ", ""))
    if not m:
        raise ValueError(f"Unsupported Fortran format descriptor: {fmt!r}")
    return int(m.group(1))


def _parse_fixed_width(lines: list[str], count: int, fmt: str, *, integer: bool) -> list:
    """Read count values stored in fixed-width Fortran fields."""
    if count == 0:
        return []
    width = _fortran_format_width(fmt)
    values = []
    for line in lines:
        # Fixed-width slicing is important: whitespace splitting breaks HB files.
        for start in range(0, len(line.rstrip("\r\n")), width):
            field = line[start:start + width].strip()
            if not field:
                continue
            try:
                if integer:
                    values.append(int(field))
                else:
                    # Fortran scientific notation may use D exponent.
                    values.append(float(field.replace("D", "E").replace("d", "e")))
            except ValueError as exc:
                raise ValueError(
                    f"Cannot parse {'integer' if integer else 'real'} field {field!r}"
                ) from exc
            if len(values) >= count:
                return values
    if len(values) < count:
        raise ValueError(f"Expected {count} values, but found {len(values)}")
    return values


def _read_hb(path: Path) -> tuple[int, list[tuple[int, int, float]]]:
    """
    Read a standard Harwell–Boeing assembled sparse matrix.
    Returns (nrows, entries), with 1-based (row, col, value) entries.
    """
    # Keep blank lines because they can be meaningful in the HB header/data layout.
    lines = path.read_text(encoding="latin-1").splitlines()
    if len(lines) < 4:
        raise ValueError("File is too short to be a Harwell–Boeing file")

    # HB line 2: total cards, pointer cards, index cards, value cards, RHS cards.
    # Counts are normally five fixed-width I14 fields. Some valid files omit
    # the trailing zero RHS count, so accept four fields and default RHS to 0.
    count_line = lines[1]
    counts = []
    for start in range(0, min(len(count_line), 70), 14):
        field = count_line[start:start + 14].strip()
        counts.append(int(field) if field else 0)
    counts = [x for x in counts if x is not None]
    if len(counts) < 4:
        counts = [int(x) for x in re.findall(r"\d+", count_line)]
    if len(counts) < 4:
        raise ValueError("Invalid HB line 2: expected at least four record counts")
    # First value is total number of data cards; following are pointer,
    # index, value and optional RHS card counts.
    ptrcrd, indcrd, valcrd = counts[1], counts[2], counts[3]
    rhscrd = counts[4] if len(counts) >= 5 else 0

    # HB line 3: mxtype (3 chars), nrow, ncol, nnzero, neltvl.
    line3 = lines[2]
    if len(line3) < 14:
        raise ValueError("Invalid HB line 3: dimensions are missing")
    mxtype = line3[:3].strip().upper()
    dims = re.findall(r"[+-]?\d+", line3[3:])
    if len(dims) < 3:
        raise ValueError("Cannot read matrix dimensions from HB header")
    nrow, ncol, nnzero = map(int, dims[:3])
    if nrow != ncol:
        raise ValueError(f"Matrix is {nrow}x{ncol}, not square; graph conversion expects square matrices")

    # HB line 4 contains up to three 16-character format descriptors.
    line4 = lines[3]
    formats = [line4[i:i + 16].strip() for i in range(0, len(line4), 16)]
    formats = [f for f in formats if f]
    if len(formats) < 2:
        # Some producers use whitespace-separated descriptors.
        formats = re.findall(r"\([^)]*\)", line4)
    if len(formats) < 2:
        raise ValueError("Cannot read HB pointer/index format descriptors")
    ptr_fmt, ind_fmt = formats[0], formats[1]
    val_fmt = formats[2] if len(formats) >= 3 else ""

    start = 4
    ptr_lines = lines[start:start + ptrcrd]
    start += ptrcrd
    ind_lines = lines[start:start + indcrd]
    start += indcrd
    val_lines = lines[start:start + valcrd]
    # RHS cards are not needed for graph structure.
    pointers = _parse_fixed_width(ptr_lines, ncol + 1, ptr_fmt, integer=True)
    indices = _parse_fixed_width(ind_lines, nnzero, ind_fmt, integer=True)

    # Pattern matrices may omit values; otherwise read numeric values.
    is_pattern = len(mxtype) >= 3 and mxtype[0] == "P"
    if is_pattern or not val_fmt or valcrd == 0:
        values = [1.0] * nnzero
    else:
        values = _parse_fixed_width(val_lines, nnzero, val_fmt, integer=False)

    entries: list[tuple[int, int, float]] = []
    for col in range(ncol):
        # HB is compressed sparse column (CSC). Pointers are 1-based.
        begin = pointers[col] - 1
        end = pointers[col + 1] - 1
        if begin < 0 or end < begin or end > nnzero:
            raise ValueError("Invalid HB column pointers")
        for k in range(begin, end):
            row = indices[k]
            if row < 1 or row > nrow:
                raise ValueError(f"Invalid row index {row} in HB matrix")
            entries.append((row, col + 1, values[k]))
    return nrow, entries


def _read_matrix_market(path: Path) -> tuple[int, list[tuple[int, int, float]]]:
    """Read Matrix Market coordinate format."""
    with path.open("r", encoding="utf-8", errors="replace") as f:
        banner = f.readline().strip().lower().split()
        if len(banner) < 5 or banner[0] != "%%matrixmarket" or banner[1] != "matrix":
            raise ValueError("Invalid Matrix Market banner")
        storage = banner[2]
        symmetry = banner[4]
        if storage != "coordinate":
            raise ValueError("Only Matrix Market coordinate format is supported")
        dims_line = ""
        for line in f:
            line = line.strip()
            if line and not line.startswith("%"):
                dims_line = line
                break
        dims = dims_line.split()
        if len(dims) < 3:
            raise ValueError("Missing Matrix Market dimensions")
        nrow, ncol, nnz = map(int, dims[:3])
        if nrow != ncol:
            raise ValueError(f"Matrix is {nrow}x{ncol}, not square")
        entries = []
        for _ in range(nnz):
            line = f.readline()
            while line and (not line.strip() or line.lstrip().startswith("%")):
                line = f.readline()
            if not line:
                raise ValueError("Matrix Market ended before all entries were read")
            parts = line.split()
            row, col = int(parts[0]), int(parts[1])
            value = float(parts[2]) if len(parts) >= 3 else 1.0
            entries.append((row, col, value))
        # Symmetric/skew/hermitian formats commonly store only one triangle.
        # The adjacency builder handles undirected mode by symmetrizing.
        return nrow, entries


def read_matrix(path: Path) -> tuple[int, list[tuple[int, int, float]]]:
    """Detect and read a supported sparse matrix file."""
    with path.open("r", encoding="latin-1", errors="replace") as f:
        first = f.readline().strip().lower()
    if first.startswith("%%matrixmarket"):
        return _read_matrix_market(path)
    return _read_hb(path)


def build_adjacency(
    n: int,
    entries: Iterable[tuple[int, int, float]],
    mode: str = "undirected",
    keep_zero: bool = False,
) -> tuple[list[set[int]], int]:
    """Build adjacency; labels are 1-based. Self-loops are ignored."""
    if mode not in {"undirected", "directed"}:
        raise ValueError("mode must be 'undirected' or 'directed'")
    adj = [set() for _ in range(n + 1)]
    for row, col, value in entries:
        if not keep_zero and value == 0:
            continue
        if row == col:
            continue
        if not (1 <= row <= n and 1 <= col <= n):
            raise ValueError(f"Index ({row}, {col}) outside 1..{n}")
        adj[row].add(col)
        if mode == "undirected":
            adj[col].add(row)
    edge_count = sum(len(adj[v]) for v in range(1, n + 1))
    if mode == "undirected":
        edge_count //= 2
    return adj, edge_count


def convert_file(
    source: Path,
    destination: Path,
    mode: str = "undirected",
    keep_zero: bool = False,
    omit_isolates: bool = False,
) -> tuple[int, int]:
    n, entries = read_matrix(source)
    adj, edge_count = build_adjacency(n, entries, mode, keep_zero)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("w", encoding="utf-8", newline="\n") as out:
        out.write(f"# source: {source.name}\n")
        out.write(f"# vertices: {n}\n")
        out.write(f"# edges: {edge_count}\n")
        out.write(f"# mode: {mode}\n")
        out.write("# format: vertex: neighbor1, neighbor2, ... (1-based labels)\n")
        for v in range(1, n + 1):
            if omit_isolates and not adj[v]:
                continue
            neighbors = ", ".join(map(str, sorted(adj[v])))
            out.write(f"{v}: {neighbors}\n")
    return n, edge_count


def discover_files(path: Path, recursive: bool = False) -> list[Path]:
    """Discover likely HB and Matrix Market files; skip generated adjacency outputs."""
    if path.is_file():
        return [path]
    if not path.is_dir():
        raise FileNotFoundError(f"Input path does not exist: {path}")
    candidates = path.rglob("*") if recursive else path.iterdir()
    allowed = {".rua", ".rsa", ".rra", ".pua", ".psa", ".mtx", ".hb", ".harwell", ".dat", ".rb"}
    files = []
    for p in candidates:
        if not p.is_file() or p.suffix.lower() not in allowed:
            continue
        # Avoid accidentally re-converting our own outputs.
        if p.stem.lower().endswith(("_adj", "_adjacency", "_converted")):
            continue
        files.append(p)
    return sorted(files)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Convert Harwell–Boeing / Matrix Market sparse matrices to adjacency lists."
    )
    parser.add_argument("input", help="Input matrix file, or directory when using --batch")
    parser.add_argument("--out", help="Output file for a single input")
    parser.add_argument("--batch", action="store_true", help="Convert every supported file in an input directory")
    parser.add_argument("--out-dir", default="adjacency", help="Output directory in batch mode (default: adjacency)")
    parser.add_argument("--recursive", action="store_true", help="Search input directory recursively in batch mode")
    parser.add_argument("--mode", choices=("undirected", "directed"), default="undirected",
                        help="undirected for graph coloring; directed to preserve matrix direction")
    parser.add_argument("--keep-zero", action="store_true",
                        help="Treat explicit zero entries as edges (normally zeros are ignored)")
    parser.add_argument("--omit-isolates", action="store_true",
                        help="Do not write vertices with no neighbors")
    args = parser.parse_args()

    source = Path(args.input)
    try:
        if args.batch:
            if not source.is_dir():
                parser.error("--batch requires input to be a directory")
            files = discover_files(source, recursive=args.recursive)
            if not files:
                print("No supported matrix files found.", file=sys.stderr)
                return 1
            out_root = Path(args.out_dir)
            successes = 0
            for file in files:
                relative = file.relative_to(source) if args.recursive else Path(file.name)
                target = out_root / relative.parent / f"{relative.stem}_adj.txt"
                try:
                    n, m = convert_file(file, target, args.mode, args.keep_zero, args.omit_isolates)
                    print(f"[OK] {file} -> {target} (vertices={n}, edges={m})")
                    successes += 1
                except Exception as exc:
                    print(f"[ERROR] {file}: {exc}", file=sys.stderr)
            print(f"Converted {successes}/{len(files)} file(s).")
            return 0 if successes == len(files) else 2

        if not source.is_file():
            parser.error(f"Input file does not exist: {source}")
        target = Path(args.out) if args.out else source.with_name(f"{source.stem}_adj.txt")
        n, m = convert_file(source, target, args.mode, args.keep_zero, args.omit_isolates)
        print(f"Converted: {source} -> {target}")
        print(f"Vertices: {n}; edges: {m}; mode: {args.mode}")
        return 0
    except Exception as exc:
        print(f"Conversion failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
