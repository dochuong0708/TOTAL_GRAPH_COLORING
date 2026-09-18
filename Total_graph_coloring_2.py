import argparse
import csv
import glob
import multiprocessing as mp
import os
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
            neighbors = list(map(int, rest.split())) if rest.strip() else []
            adj[u] = neighbors
    if not adj:
        return {}

    n = max(adj.keys())
    for v in range(1, n + 1):
        if v not in adj:
            adj[v] = []

    for u in list(adj.keys()):
        for v in adj[u]:
            if 1 <= v <= n and u not in adj[v]:
                adj[v].append(u)

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
    for i in range(total_num):
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
    return total_num, total_adj, delta, num_v, num_e


def build_direct_cnf(total_num, total_adj, k, use_symmetry_breaking=True):
    x = {}
    nv = 0
    for o in range(total_num):
        for i in range(1, k + 1):
            nv += 1
            x[(o, i)] = nv

    clauses = []


    for o in range(total_num):
        clauses.append([x[(o, i)] for i in range(1, k + 1)])


    for o in range(total_num):
        for i in range(1, k + 1):
            for j in range(i + 1, k + 1):
                clauses.append([-x[(o, i)], -x[(o, j)]])

    for u in range(total_num):
        for v in total_adj[u]:
            if v <= u:
                continue
            for i in range(1, k + 1):
                clauses.append([-x[(u, i)], -x[(v, i)]])

    if use_symmetry_breaking and k >= 2:
        u0 = max(total_adj.keys(), key=lambda v: len(total_adj[v]))
        max_allowed_color = (k + 1) // 2
        for c in range(max_allowed_color + 1, k + 1):
            clauses.append([-x[(u0, c)]])

    return clauses, nv, x


def solver_worker_incremental(
    total_num, total_adj, delta, solver_name, queue, use_symmetry_breaking=True
):
    try:
        k2 = delta + 2
        k1 = delta + 1

        t0_enc = time.time()
        clauses, nv, x = build_direct_cnf(
            total_num, total_adj, k2, use_symmetry_breaking
        )
        t_enc = time.time() - t0_enc

        solver = Solver(name=solver_name, bootstrap_with=clauses)

        t0_sol2 = time.time()
        sat2 = solver.solve()
        t_sol2 = time.time() - t0_sol2

        res2 = {
            "status": "SAT" if sat2 else "UNSAT",
            "t_enc": t_enc,
            "t_sol": t_sol2,
            "clauses": len(clauses),
            "vars": nv,
        }
        queue.put(("STEP1_DONE", res2))

        if not sat2:
            solver.delete()
            return

        extra_unit_clauses = [[-x[(u, k2)]] for u in range(total_num)]
        for cl in extra_unit_clauses:
            solver.add_clause(cl)

        t0_sol1 = time.time()
        sat1 = solver.solve()
        t_sol1 = time.time() - t0_sol1

        solver.delete()

        res1 = {
            "status": "SAT" if sat1 else "UNSAT",
            "t_enc": 0.0,
            "t_sol": t_sol1,
            "clauses": len(clauses) + len(extra_unit_clauses),
            "vars": nv,
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

    total_num, total_adj, delta, num_v, num_e = build_total_graph(adj)
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
        target=solver_worker_incremental,
        args=(total_num, total_adj, delta, solver_name, q),
    )

    p.start()

    res2, res1 = None, None
    has_error = False

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
                if verbose:
                    print(f" => LỖI SOLVER: {data}")
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
                t_solving_total += res1["t_sol"]
                vars_count, clauses_count = res1["vars"], res1["clauses"]
                history.append(
                    {
                        "k": k1,
                        "status": res1["status"],
                        "time_sec": round(res1["t_sol"], 2),
                    }
                )
                if verbose:
                    print(
                        f" k={k1:>3} -> {res1['status']:<8}"
                        f" ({res1['t_sol']:8.2f}s)"
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
        final_status = "unsat"
        chi_T = None

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
            "Tim so mau nho nhat cho Total Coloring bang SAT (Direct Encoding"
            " Incremental)."
        )
    )
    parser.add_argument(
        "--data-dir",
        required=True,
        help="Thu muc chua cac file do thi dang .lst hoac .txt.",
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
    parser.add_argument("--out", default=None, help="File CSV de ghi ket qua.")
    parser.add_argument(
        "--solver",
        default="cadical153",
        help=(
            "Ten SAT solver backend cua pysat (cadical153, glucose4, minisat22,"
            " ...)."
        ),
    )
    args = parser.parse_args()

    out_csv = (
        args.out
        or f"direct_incremental_results_{datetime.now():%Y%m%d_%H%M%S}.csv"
    )
    run_batch(args.data_dir, args.timeout, out_csv, solver_name=args.solver)


if __name__ == "__main__":
    main()