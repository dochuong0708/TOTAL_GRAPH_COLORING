import argparse
import csv
import glob
import multiprocessing as mp
import os
import time
from datetime import datetime
import gurobipy as gp
import re
from gurobipy import GRB


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



def solve_total_coloring_gurobi(
    adj, timeout_sec=1800, instance_name="graph", t0_start=None
):
    """
    Hàm khởi tạo mô hình MIP và giải bằng Gurobi.
    Tất cả biến và ràng buộc đều được khởi tạo cục bộ bên trong hàm này.
    """
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

    # Sử dụng with gp.Env để tự động nhận gurobi.lic trong thư mục User và dọn dẹp tài nguyên
    with gp.Env(empty=True) as env:
        env.setParam("OutputFlag", 0)  # Tắt log console
        env.start()

        with gp.Model(instance_name, env=env) as model:
            # Khai báo biến quyết định cục bộ
            w = model.addVars(colors, vtype=GRB.BINARY, name="w")
            x = model.addVars(vertices, colors, vtype=GRB.BINARY, name="x")
            y = model.addVars(num_e, colors, vtype=GRB.BINARY, name="y")

            # Hàm mục tiêu: Tối thiểu hóa số màu
            model.setObjective(gp.quicksum(w[c] for c in colors), GRB.MINIMIZE)

            # Ràng buộc 1: Mỗi đỉnh được tô đúng 1 màu
            model.addConstrs(
                (gp.quicksum(x[v, c] for c in colors) == 1 for v in vertices),
                name="v_color",
            )

            # Ràng buộc 2: Mỗi cạnh được tô đúng 1 màu
            model.addConstrs(
                (
                    gp.quicksum(y[eid, c] for c in colors) == 1
                    for eid in range(num_e)
                ),
                name="e_color",
            )

            # Ràng buộc 3: Hai đỉnh kề nhau không cùng màu
            model.addConstrs(
                (x[u, c] + x[v, c] <= w[c] for u, v in edges for c in colors),
                name="adj_v",
            )

            # Ràng buộc 4 (CẢI TIẾN): Ràng buộc Hình Sao (Star Constraint)
            # Đỉnh v và TẤT CẢ các cạnh liên thuộc v phải mang các màu khác nhau
            model.addConstrs(
                (
                    x[v, c] + gp.quicksum(y[eid, c] for eid in incident_at[v])
                    <= w[c]
                    for v in vertices
                    for c in colors
                ),
                name="star_constr",
            )

            model.update()
            t_encoding = time.time() - t0_enc

            vars_count = model.NumVars
            clauses_count = model.NumConstrs

            # 2. GIẢI MÔ HÌNH (SOLVING)
            # Tính thời gian còn lại thực tế dành riêng cho Gurobi solve
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

            model.setParam("TimeLimit", remaining_time)
            model.optimize()

            t_solving = model.Runtime
            t_total = time.time() - t0_start

            status_code = model.status
            chi_T = "UNKNOWN"
            final_status = "timeout"

            if status_code == GRB.OPTIMAL:
                final_status = "optimal"
                chi_T = int(round(model.ObjVal))
            elif status_code == GRB.TIME_LIMIT:
                final_status = "timeout"
                if model.SolCount > 0:
                    chi_T = int(round(model.ObjVal))
            elif status_code == GRB.INFEASIBLE:
                final_status = "unsat"
            else:
                final_status = f"status_{status_code}"

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


def worker_task(path, timeout_sec, result_queue):
    """
    Hàm worker chạy độc lập trong một Process riêng.
    Cô lập hoàn toàn bộ nhớ và thời gian của từng file đồ thị.
    """
    t0_start = time.time()
    name = os.path.splitext(os.path.basename(path))[0]
    try:
        adj = read_file_graph(path)
        if not adj:
            result_queue.put({"instance_name": name, "status": "empty_file"})
            return

        res = solve_total_coloring_gurobi(
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
    Quản lý tiến trình chạy với Hard Timeout 1800s tuyệt đối.
    Nếu thời gian chạy vượt quá timeout_sec, KILL Process ngay lập tức.
    """
    t0 = time.time()
    name = os.path.splitext(os.path.basename(path))[0]
    ctx = mp.get_context("spawn")
    queue = ctx.Queue()

    p = ctx.Process(target=worker_task, args=(path, timeout_sec, queue))
    p.start()
    p.join(timeout=timeout_sec)

    # Nếu Process vẫn còn chạy sau timeout_sec -> Ép ngắt cứng (Kill Process)
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
        description="Tim so mau nho nhat cho Total Coloring bang Quy hoach so nguyen (Gurobi MIP)."
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
        help="File CSV de ghi ket qua. Mac dinh: gurobi_results_<timestamp>.csv",
    )
    args = parser.parse_args()

    out_csv = args.out or f"gurobi_results_{datetime.now():%Y%m%d_%H%M%S}.csv"
    run_batch(args.data_dir, args.timeout, out_csv)


if __name__ == "__main__":
    main()