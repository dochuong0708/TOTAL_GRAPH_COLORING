import argparse
import csv
import glob
import multiprocessing as mp
import os
import re
import time
from datetime import datetime
from pysat.solvers import Solver


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


def build_total_graph(adj):
    total_adj = {}
    n = len(adj)
    vertices = list(range(1, n + 1))

    edges = []
    for u in vertices:
        for v in adj[u]:
            if u < v:
                edges.append((u, v))
    num_v, num_e = n, len(edges)
    total_num = num_v + num_e
    for i in range(0, total_num):
        total_adj[i] = set()

    for u in vertices:
        for v in adj[u]:
            if u != v:
                total_adj[u - 1].add(v - 1)

    incident_at = {v: [] for v in vertices}
    for idx, (u, v) in enumerate(edges):
        eid = num_v + idx
        total_adj[u - 1].add(eid)
        total_adj[eid].add(u - 1)
        total_adj[v - 1].add(eid)
        total_adj[eid].add(v - 1)

        incident_at[u].append(idx)
        incident_at[v].append(idx)

    for v in vertices:
        inc = incident_at[v]
        for i in range(len(inc)):
            for j in range(i + 1, len(inc)):
                e1, e2 = num_v + inc[i], num_v + inc[j]
                total_adj[e1].add(e2)
                total_adj[e2].add(e1)

    delta = max((len(adj[v]) for v in vertices), default=0)
    return total_num, total_adj, delta, num_v, num_e, edges


def build_cnf_order(total_num, total_adj, k, use_symmetry_breaking=True):
    y, x = {}, {}
    nv = 0
    for u in range(total_num):
        for j in range(1, k + 1):
            nv += 1
            y[(u, j)] = nv
        for j in range(1, k + 1):
            nv += 1
            x[(u, j)] = nv

    clauses = []
    for u in range(total_num):
        for j in range(1, k + 1):
            xu, yu = x[(u, j)], y[(u, j)]
            if j < k:
                yu1 = y[(u, j + 1)]
                clauses.append([-xu, yu])
                clauses.append([-xu, -yu1])
                clauses.append([-yu, yu1, xu])
            else:
                clauses.append([-xu, yu])
                clauses.append([-yu, xu])

        clauses.append([y[(u, 1)]])

    for u in range(total_num):
        for j in range(2, k + 1):
            clauses.append([-y[(u, j)], y[(u, j - 1)]])

    for u in range(total_num):
        for v in total_adj[u]:
            if v <= u:
                continue
            for j in range(1, k + 1):
                xu = x[(u, j)]
                if j < k:
                    yv, yv1 = y[(v, j)], y[(v, j + 1)]
                    clauses.append([-xu, -yv, yv1])
                else:
                    yv = y[(v, k)]
                    clauses.append([-xu, -yv])

    if use_symmetry_breaking and k >= 2:
        u0 = max(total_adj.keys(), key=lambda v: len(total_adj[v]))
        mid_idx = (k + 1) // 2 + 1
        if mid_idx <= k:
            clauses.append([-y[(u0, mid_idx)]])

    return clauses, nv, x, y


def extract_coloring(model, total_num, k, x):
    if model is None:
        return None
    model_set = set(model)
    colors = {}
    for u in range(total_num):
        for j in range(1, k + 1):
            if x[(u, j)] in model_set:
                colors[u] = j
                break
    return colors


def verify_total_coloring(adj, edges, num_v, num_e, total_num, delta, k, colors):
    errors = []
    if not colors or len(colors) < total_num:
        return {"is_valid": False, "errors": ["Dữ liệu tô màu không đầy đủ."]}

    if k < delta + 1:
        errors.append(
            f"[Lỗi Lý Thuyết] k = {k} nhỏ hơn giới hạn dưới Delta + 1 ="
            f" {delta + 1}"
        )

    for u in range(1, num_v + 1):
        for v in adj[u]:
            if u < v:
                if colors[u - 1] == colors[v - 1]:
                    errors.append(
                        f"[Lỗi Đỉnh-Đỉnh] Đỉnh {u} và Đỉnh {v} kề nhau cùng"
                        f" màu {colors[u - 1]}"
                    )

    for idx, (u, v) in enumerate(edges):
        eid = num_v + idx
        c_e, c_u, c_v = colors[eid], colors[u - 1], colors[v - 1]
        if c_u == c_e:
            errors.append(
                f"[Lỗi Đỉnh-Cạnh] Đỉnh {u} và Cạnh ({u}, {v}) cùng màu {c_u}"
            )
        if c_v == c_e:
            errors.append(
                f"[Lỗi Đỉnh-Cạnh] Đỉnh {v} và Cạnh ({u}, {v}) cùng màu {c_v}"
            )

    incident_edges = {v: [] for v in range(1, num_v + 1)}
    for idx, (u, v) in enumerate(edges):
        eid = num_v + idx
        incident_edges[u].append(eid)
        incident_edges[v].append(eid)

    for v in range(1, num_v + 1):
        v_idx = v - 1
        local_elements = [v_idx] + incident_edges[v]
        local_colors = [colors[e] for e in local_elements]
        if len(local_colors) != len(set(local_colors)):
            errors.append(
                f"[Lỗi Clique Đỉnh {v}] Đỉnh {v} và các cạnh liên thuộc có màu"
                f" bị trùng: {local_colors}"
            )

    used_colors = set(colors.values())
    return {
        "is_valid": len(errors) == 0,
        "errors": errors,
        "num_colors_used": len(used_colors),
        "colors_used_list": sorted(list(used_colors)),
    }


def print_coloring_solution(num_v, edges, colors):
    print("\n--- PHÂN BỔ MÀU CHI TIẾT ---")
    print("[Đỉnh]:")
    for u in range(1, num_v + 1):
        print(f"  • Đỉnh {u:>2}: Màu {colors[u - 1]}")
    print("[Cạnh]:")
    for idx, (u, v) in enumerate(edges):
        eid = num_v + idx
        print(f"  • Cạnh ({u:>2}, {v:>2}): Màu {colors[eid]}")
    print("----------------------------\n")


def solver_worker(
    total_num, total_adj, delta, solver_name, queue, use_symmetry_breaking=True
):
    try:
        k2 = delta + 2
        k1 = delta + 1

        # 1. BƯỚC 1: Mã hóa và Giải k = Delta + 2 độc lập
        t0_enc2 = time.time()
        clauses2, nv2, x2, _ = build_cnf_order(
            total_num, total_adj, k2, use_symmetry_breaking
        )
        t_enc2 = time.time() - t0_enc2

        solver2 = Solver(name=solver_name, bootstrap_with=clauses2)
        t0_sol2 = time.time()
        sat2 = solver2.solve()
        t_sol2 = time.time() - t0_sol2

        colors2 = None
        if sat2:
            model2 = solver2.get_model()
            colors2 = extract_coloring(model2, total_num, k2, x2)
        solver2.delete()

        res2 = {
            "status": "SAT" if sat2 else "UNSAT",
            "t_enc": t_enc2,
            "t_sol": t_sol2,
            "clauses": len(clauses2),
            "vars": nv2,
            "colors": colors2,
            "k": k2,
        }
        queue.put(("STEP1_DONE", res2))

        # 2. BƯỚC 2: Mã hóa và Giải k = Delta + 1 độc lập từ đầu
        t0_enc1 = time.time()
        clauses1, nv1, x1, _ = build_cnf_order(
            total_num, total_adj, k1, use_symmetry_breaking
        )
        t_enc1 = time.time() - t0_enc1

        solver1 = Solver(name=solver_name, bootstrap_with=clauses1)
        t0_sol1 = time.time()
        sat1 = solver1.solve()
        t_sol1 = time.time() - t0_sol1

        colors1 = None
        if sat1:
            model1 = solver1.get_model()
            colors1 = extract_coloring(model1, total_num, k1, x1)
        solver1.delete()

        res1 = {
            "status": "SAT" if sat1 else "UNSAT",
            "t_enc": t_enc1,
            "t_sol": t_sol1,
            "clauses": len(clauses1),
            "vars": nv1,
            "colors": colors1,
            "k": k1,
        }
        queue.put(("STEP2_DONE", res1))

    except Exception as e:
        queue.put(("ERROR", str(e)))


def find_total_chromatic_number(
    adj,
    timeout_sec=1800,
    t_instance_start=None,
    verbose=True,
    solver_name="cadical153",
):
    if t_instance_start is None:
        t_instance_start = time.time()

    total_num, total_adj, delta, num_v, num_e, edges = build_total_graph(adj)
    k2 = delta + 2
    k1 = delta + 1

    history = []
    chi_T = None
    final_status = "timeout"
    t_encoding_total = 0.0
    t_solving_total = 0.0
    vars_count = 0
    clauses_count = 0

    ctx = mp.get_context("spawn")
    q = ctx.Queue()

    p = ctx.Process(
        target=solver_worker,
        args=(total_num, total_adj, delta, solver_name, q),
    )
    p.start()

    res2, res1 = None, None
    has_error = False
    error_msg = ""

    while True:
        rem_time = timeout_sec - (time.time() - t_instance_start)
        if rem_time <= 0:
            if p.is_alive():
                p.kill()
                p.join()
            break

        p.join(timeout=min(0.5, max(0.1, rem_time)))

        while not q.empty():
            tag, data = q.get()
            if tag == "ERROR":
                has_error = True
                error_msg = data
                if verbose:
                    print(f" => LỖI SOLVER: {error_msg}")
                break
            elif tag == "STEP1_DONE":
                res2 = data
                t_encoding_total += res2["t_enc"]
                t_solving_total += res2["t_sol"]
                vars_count, clauses_count = res2["vars"], res2["clauses"]
                history.append(
                    {
                        "k": k2,
                        "status": res2["status"],
                        "time_sec": round(res2["t_enc"] + res2["t_sol"], 2),
                    }
                )
                if verbose:
                    print(
                        f" k={k2:>3} -> {res2['status']:<8}"
                        f" ({res2['t_enc'] + res2['t_sol']:8.2f}s)"
                    )

            elif tag == "STEP2_DONE":
                res1 = data
                t_encoding_total += res1["t_enc"]
                t_solving_total += res1["t_sol"]
                vars_count, clauses_count = res1["vars"], res1["clauses"]
                history.append(
                    {
                        "k": k1,
                        "status": res1["status"],
                        "time_sec": round(res1["t_enc"] + res1["t_sol"], 2),
                    }
                )
                if verbose:
                    print(
                        f" k={k1:>3} -> {res1['status']:<8}"
                        f" ({res1['t_enc'] + res1['t_sol']:8.2f}s)"
                    )

        if has_error or not p.is_alive():
            break

    q.close()
    q.cancel_join_thread()

    if has_error:
        final_status = "error"
        chi_T = None
    elif res2 is None:
        final_status = "timeout"
        chi_T = None
    elif res2["status"] == "SAT":
        if res1 is None:
            final_status = "timeout"
            chi_T = k2
        elif res1["status"] == "SAT":
            final_status = "optimal"
            chi_T = k1
        elif res1["status"] == "UNSAT":
            final_status = "optimal"
            chi_T = k2
    elif res2["status"] == "UNSAT":
        if res1 is None:
            final_status = "timeout"
            chi_T = k1
        else:
            final_status = "unsat"
            chi_T = None

    best_res = (
        res1
        if (res1 and res1["status"] == "SAT")
        else (res2 if (res2 and res2["status"] == "SAT") else None)
    )
    if best_res and best_res["colors"]:
        colors = best_res["colors"]
        if verbose:
            print_coloring_solution(num_v, edges, colors)
        v_report = verify_total_coloring(
            adj, edges, num_v, num_e, total_num, delta, best_res["k"], colors
        )
        if v_report["is_valid"]:
            print(
                f" => XÁC NHẬN BẢO ĐẢM: Lời giải k={best_res['k']} HOÀN TOÀN HỢP LỆ!"
            )
            print(
                f"    Số màu thực tế sử dụng: {v_report['num_colors_used']}"
                f" {v_report['colors_used_list']}"
            )
        else:
            print(
                f" => PHÁT HIỆN {len(v_report['errors'])} LỖI TRONG LỜI GIẢI:"
            )
            for err in v_report["errors"]:
                print("   ", err)

    total_elapsed = time.time() - t_instance_start

    return {
        "n": num_v,
        "m": num_e,
        "delta": delta,
        "chi_T": chi_T,
        "vars": vars_count,
        "clauses": clauses_count,
        "t_encoding_sec": round(t_encoding_total, 2),
        "t_solving_sec": round(t_solving_total, 2),
        "t_total_sec": round(total_elapsed, 2),
        "status": final_status,
        "span": chi_T if chi_T is not None else "UNKNOWN",
        "history": history,
    }


def run_batch(data_dir, timeout_sec, out_csv, solver_name="cadical153"):
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

        t_instance_start = time.time()

        adj = read_file_graph(path)
        if not adj:
            print("(file rong, khong co data)")
            continue

        result = find_total_chromatic_number(
            adj,
            timeout_sec=timeout_sec,
            t_instance_start=t_instance_start,
            solver_name=solver_name,
        )

        row = {
            "instance_name": name,
            "|V|": result["n"],
            "|E|": result["m"],
            "vars": result["vars"],
            "clauses": result["clauses"],
            "t_encoding": result["t_encoding_sec"],
            "t_solving": result["t_solving_sec"],
            "t_total": result["t_total_sec"],
            "status": result["status"],
            "span": result["span"],
            "delta": result["delta"],
            "chi_T": (
                result["chi_T"] if result["chi_T"] is not None else "UNKNOWN"
            ),
        }
        rows.append(row)

        print(
            f" => {name}: status={row['status']}, span={row['span']}, delta ="
            f" {result['delta']}, chi_T={result['chi_T']},"
            f" t_total={row['t_total']:.2f}s"
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
        description=(
            "Tim so mau nho nhat cho Total Coloring bang SAT (CNF order"
            " encoding)."
        )
    )
    parser.add_argument(
        "--data-dir",
        required=True,
        help=(
            "Thu muc chua cac file do thi dang .lst hoac .txt (danh sach ke,"
            " 1-indexed)."
        ),
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=1800,
        help=(
            "Thoi gian toi da (giay) cho MOI file do thi. Mac dinh 1800s = 30"
            " phut."
        ),
    )
    parser.add_argument(
        "--out",
        default=None,
        help=(
            "File CSV de ghi ket qua. Mac dinh:"
            " total_coloring_results_<timestamp>.csv"
        ),
    )
    parser.add_argument(
        "--solver",
        default="cadical153",
        help=(
            "Ten SAT solver backend cua pysat (glucose3, glucose4, cadical153,"
            " minisat22, ...). Mac dinh: cadical153."
        ),
    )
    args = parser.parse_args()

    out_csv = (
        args.out or f"total_coloring_results_{datetime.now():%Y%m%d_%H%M%S}.csv"
    )
    run_batch(args.data_dir, args.timeout, out_csv, solver_name=args.solver)


if __name__ == "__main__":
    main()