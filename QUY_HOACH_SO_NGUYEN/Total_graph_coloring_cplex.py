import argparse
import csv
import glob
import multiprocessing as mp
import os
import re
import time
from datetime import datetime
from docplex.mp.model import Model


def read_file_graph(path):
    adj = {}
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or ":" not in line:
                continue
            head, _, rest = line.partition(":")
            try:
                u = int(head.strip())
            except ValueError:
                continue
            neighbors = [int(x) for x in re.findall(r"\d+", rest)]
            adj[u] = neighbors
    if not adj:
        return {}
    n = max(adj.keys())
    for v in range(1, n + 1):
        if v not in adj:
            adj[v] = []
    return adj




def solve_total_coloring_cplex(
    adj, timeout_sec=1800, instance_name="graph", t0_start=None
):
    if t0_start is None:
        t0_start = time.time()

    n = len(adj)
    vertices = list(range(1, n + 1))

    # Trích xuất danh sách các cạnh (u < v)
    edges = []
    for u in vertices:
        for v in adj[u]:
            if u < v:
                edges.append((u, v))

    num_v, num_e = n, len(edges)
    delta = max((len(adj[v]) for v in vertices), default=0)

    # Miền màu tối đa theo định lý Behzad (span = Delta + 2)
    span = delta + 2
    colors = list(range(span))

    # Danh sách các cạnh liên thuộc với từng đỉnh (lưu chỉ số eid)
    incident_at = {v: [] for v in vertices}
    for eid, (u, v) in enumerate(edges):
        incident_at[u].append(eid)
        incident_at[v].append(eid)

    # 1. MÃ HÓA MÔ HÌNH (ENCODING)
    t0_enc = time.time()

    model = Model(name=instance_name)
    model.context.solver.log_output = False  # Tắt log console

    try:
        # Khai báo biến quyết định cục bộ
        w = model.binary_var_dict(colors, name="w")
        x = model.binary_var_dict(
            [(v, c) for v in vertices for c in colors], name="x"
        )
        y = model.binary_var_dict(
            [(eid, c) for eid in range(num_e) for c in colors], name="y"
        )

        # Hàm mục tiêu: Tối thiểu hóa số màu
        model.minimize(model.sum(w[c] for c in colors))

        # --- CHÈN RÀNG BUỘC HÀNG LOẠT (TỐI ƯU TỐC ĐỘ) ---

        # Ràng buộc 1: Mỗi đỉnh đúng 1 màu
        model.add_constraints(
            model.sum(x[v, c] for c in colors) == 1 for v in vertices
        )

        # Ràng buộc 2: Mỗi cạnh đúng 1 màu
        model.add_constraints(
            model.sum(y[eid, c] for c in colors) == 1 for eid in range(num_e)
        )

        # Ràng buộc 3: Hai đỉnh kề nhau không cùng màu
        model.add_constraints(
            x[u, c] + x[v, c] <= w[c] for u, v in edges for c in colors
        )

        # Ràng buộc 4 (TỐI ƯU): Ràng buộc Hình Sao (Star Constraint)
        # Tại mỗi đỉnh v, đỉnh v và tất cả các cạnh liên thuộc v phải có màu khác nhau.
        model.add_constraints(
            x[v, c] + model.sum(y[eid, c] for eid in incident_at[v]) <= w[c]
            for v in vertices
            for c in colors
        )

        t_encoding = time.time() - t0_enc

        vars_count = model.number_of_variables
        clauses_count = model.number_of_constraints

        # 2. GIẢI MÔ HÌNH (SOLVING)
        # Tính thời gian còn lại dành riêng cho CPLEX
        elapsed_so_far = time.time() - t0_start
        remaining_time = timeout_sec - elapsed_so_far

        if remaining_time <= 0.5:
            return {
                "instance_name": instance_name,
                "n": num_v,
                "m": num_e,
                "delta": delta,
                "chi_T": "UNKNOWN",
                "vars": vars_count,
                "clauses": clauses_count,
                "t_encoding_sec": round(t_encoding, 2),
                "t_solving_sec": 0.0,
                "t_total_sec": round(time.time() - t0_start, 2),
                "status": "timeout",
                "span": span,
            }

        model.time_limit = remaining_time

        sol = model.solve()

        solve_details = model.get_solve_details()
        t_solving = solve_details.time
        t_total = time.time() - t0_start

        status_str = str(solve_details.status).lower()
        chi_T = "UNKNOWN"
        final_status = "timeout"

        if sol is not None:
            chi_T = int(round(sol.objective_value))
            if "optimal" in status_str:
                final_status = "optimal"
            else:
                final_status = "timeout"
        else:
            if "infeasible" in status_str:
                final_status = "unsat"
            elif "time limit" in status_str or "limit" in status_str:
                final_status = "timeout"
            else:
                final_status = status_str

        return {
            "instance_name": instance_name,
            "n": num_v,
            "m": num_e,
            "delta": delta,
            "chi_T": chi_T,
            "vars": vars_count,
            "clauses": clauses_count,
            "t_encoding_sec": round(t_encoding, 2),
            "t_solving_sec": round(t_solving, 2),
            "t_total_sec": round(t_total, 2),
            "status": final_status,
            "span": span,
        }
    finally:
        # Giải phóng bộ nhớ CPLEX C++ giải phóng tài nguyên triệt để
        model.end()


def worker_task(path, timeout_sec, result_queue):
    """Hàm chạy trong Process riêng biệt để đảm bảo cô lập tuyệt đối."""
    t0_start = time.time()
    name = os.path.splitext(os.path.basename(path))[0]
    try:
        adj = read_file_graph(path)
        if not adj:
            result_queue.put({"instance_name": name, "status": "empty_file"})
            return

        res = solve_total_coloring_cplex(
            adj, timeout_sec=timeout_sec, instance_name=name, t0_start=t0_start
        )
        result_queue.put(res)
    except Exception as e:
        result_queue.put(
            {
                "instance_name": name,
                "status": "error",
                "t_total_sec": round(time.time() - t0_start, 2),
                "error": str(e),
            }
        )


def run_single_instance_with_timeout(path, timeout_sec):
    """
    Chạy từng file trong một tiến trình độc lập với Hard Timeout.
    Nếu thời gian vượt quá timeout_sec (bao gồm đọc file + mã hóa + giải), kill process lập tức.
    """
    t0 = time.time()
    name = os.path.splitext(os.path.basename(path))[0]
    ctx = mp.get_context("spawn")
    queue = ctx.Queue()

    p = ctx.Process(target=worker_task, args=(path, timeout_sec, queue))
    p.start()
    p.join(timeout=timeout_sec)

    if p.is_alive():
        p.terminate()
        p.join()
        t_total = time.time() - t0
        return {
            "instance_name": name,
            "n": "N/A",
            "m": "N/A",
            "delta": "N/A",
            "chi_T": "UNKNOWN",
            "vars": "N/A",
            "clauses": "N/A",
            "t_encoding_sec": "N/A",
            "t_solving_sec": "N/A",
            "t_total_sec": round(t_total, 2),
            "status": "timeout",
            "span": "N/A",
        }

    if not queue.empty():
        return queue.get()

    return {
        "instance_name": name,
        "n": "N/A",
        "m": "N/A",
        "delta": "N/A",
        "chi_T": "UNKNOWN",
        "vars": "N/A",
        "clauses": "N/A",
        "t_encoding_sec": "N/A",
        "t_solving_sec": "N/A",
        "t_total_sec": round(time.time() - t0, 2),
        "status": "error",
        "span": "N/A",
    }


def run_batch(data_dir, timeout_sec, out_csv):
    supported_exts = (".lst", ".txt")
    files = []
    for ext in supported_exts:
        files.extend(glob.glob(os.path.join(data_dir, f"*{ext}")))
    files = sorted(files)

    if not files:
        print(f"Khong tim thay file do thi (.lst/.txt) nao trong: {data_dir}")
        return

    fieldnames = [
        "instance_name",
        "|V|",
        "|E|",
        "vars",
        "clauses",
        "t_encoding",
        "t_solving",
        "t_total",
        "status",
        "span",
        "delta",
        "chi_T",
    ]
    rows = []

    for path in files:
        name = os.path.splitext(os.path.basename(path))[0]
        print(f"\n==={name}===")

        result = run_single_instance_with_timeout(path, timeout_sec)

        row = {
            "instance_name": name,
            "|V|": result.get("n", "N/A"),
            "|E|": result.get("m", "N/A"),
            "vars": result.get("vars", "N/A"),
            "clauses": result.get("clauses", "N/A"),
            "t_encoding": result.get("t_encoding_sec", "N/A"),
            "t_solving": result.get("t_solving_sec", "N/A"),
            "t_total": result.get("t_total_sec", "N/A"),
            "status": result.get("status", "unknown"),
            "span": result.get("span", "N/A"),
            "delta": result.get("delta", "N/A"),
            "chi_T": result.get("chi_T", "UNKNOWN"),
        }
        rows.append(row)

        print(
            f" => {name}: status={row['status']}, span={row['span']}, delta={row['delta']}, "
            f"chi_T={row['chi_T']}, t_total={row['t_total']}s"
        )

        parent_dir = os.path.dirname(out_csv)
        if parent_dir:
            os.makedirs(parent_dir, exist_ok=True)

        with open(out_csv, "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(rows)

    print(f"\nDa ghi ket qua vao: {out_csv}")


def main():
    parser = argparse.ArgumentParser(
        description="Tim so mau nho nhat cho Total Coloring bang Quy hoach so nguyen (CPLEX MIP)."
    )
    parser.add_argument(
        "--data-dir",
        required=True,
        help="Thu muc chua cac file do thi dang .lst hoac .txt (danh sach ke, 1-indexed).",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=1800,
        help="Thoi gian toi da (giay) cho MOI file do thi. Mac dinh 1800s = 30 phut.",
    )
    parser.add_argument(
        "--out",
        default=None,
        help="File CSV de ghi ket qua. Mac dinh: cplex_results_<timestamp>.csv",
    )
    args = parser.parse_args()

    out_csv = args.out or f"cplex_results_{datetime.now():%Y%m%d_%H%M%S}.csv"
    run_batch(args.data_dir, args.timeout, out_csv)


if __name__ == "__main__":
    main()