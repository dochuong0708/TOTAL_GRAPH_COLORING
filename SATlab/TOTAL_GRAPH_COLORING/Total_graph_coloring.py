import argparse
import multiprocessing as mp
import csv
import glob
import os
import time
from datetime import datetime


from pysat.solvers import Solver

# doc file chua data 
def read_file_graph(path):
    adj = {}
    with open(path, "r", encoding = "utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if ":" not in line:
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
    return adj

# xay dung mot do thi tong quat
'''
Ham tra ve:
  total_num: int, tong so dinh(n) va canh(m) cua do thi
  total_adj: dict, trong do:
            ~ key(0 -> n-1): int, dinh cua do thi
            ~ key(n -> n + m - 1): int, canh cua do thi
            ~ value: list, danh sach hang xom cua cac dinh va canh  
'''
 
def build_total_graph(adj):
    total_adj = {}
    n = len(adj)
    vertices = list(range(1, n + 1))


    edges = []
    for u in vertices:
        for v in adj[u]:
            if u < v:
                edges.append((u,v))
    num_v, num_e = n, len(edges)
    total_num = num_v + num_e
    for i in range(0, total_num):
        total_adj[i] = set()
    
    # danh sach cac dinh ke nhau (neu co canh) 
    for u in vertices:
        for v in adj[u]:
            if u!=v:
                total_adj[u-1].add(v-1)

    # danh sach cac dinh va canh ke nhau
    incident_at = {v: [] for v in vertices}
    for idx, (u,v) in enumerate(edges):
        eid = num_v + idx #id cua canh trong do thi

        # noi dinh voi canh ma chung lien thuoc 
        total_adj[u-1].add(eid)
        total_adj[eid].add(u-1)
        total_adj[v-1].add(eid)
        total_adj[eid].add(v-1)

        # luu lai danh sach dinh va canh ke nhau 
        '''
        Vi du: 1:[2,3] co nghia la dinh 1 ke voi canh 2 va 3
        ''' 
        incident_at[u].append(idx)
        incident_at[v].append(idx)

    # canh ke nhau
    for v in vertices:
        inc = incident_at[v]
        for i in range(len(inc)):
            for j in range(i + 1, len(inc)):
                e1, e2 = num_v + inc[i], num_v + inc[j]
                total_adj[e1].add(e2)
                total_adj[e2].add(e1)

    delta = max((len(adj[v]) for v in vertices ), default = 0)
    return total_num, total_adj, delta, num_v, num_e
'''
Sinh ra cnf theo yeu cau bai toan
'''
def  build_cnf(total_num, total_adj, k):
    """
    Sinh ra danh sach menh de CNF cho bai toan total-coloring voi k mau
    Bien:
        y[(u,j)] cho j = 1,..,k  (mau(u) >= j)
        x[(u,j)] cho j = 1,..,k  (mau(u) == j)
    """

    y, x ={}, {}
    nv = 0
    for u in range(total_num):
        for j in range(1, k + 1):
            nv+=1
            y[(u,j)] = nv
        for j in range(1, k + 1):
            nv+=1
            x[(u,j)] = nv

    clauses = []

    for u in range(total_num):
        for j in range(1, k+1):
            xu, yu = x[(u,j)], y[(u,j)]
            if j<k:
                yu1 = y[(u,j+1)]
                clauses.append([-xu,yu])
                clauses.append([-xu,-yu1])
                clauses.append([-yu, yu1, xu])
            else:
                clauses.append([-xu, yu])
                clauses.append([-yu, xu])

        clauses.append([y[(u,1)]])

    for u in range(total_num):
        for j in range(2, k + 1):
            clauses.append([-y[(u,j)], y[(u,j - 1)]])

    for u in range(total_num):
        for v in total_adj[u]:
            if v<=u:
                continue
            for j in range(1,k+1):
                xu = x[(u,j)]
                if j < k:
                    yv, yv1 = y[(v,j)], y[(v,j+1)]
                    clauses.append([-xu,-yv,yv1])
                else:
                    yv = y[(v,k)]
                    clauses.append([-xu,-yv])

    return clauses, nv

def solver_worker(clauses, nv, solver_name, queue):
    try:
        solver = Solver(name=solver_name)
        for c in clauses:
            solver.add_clause(c)
        sat = solver.solve()
        model = solver.get_model() if sat else None
        solver.delete()
        queue.put(("Done", sat, model))
    except Exception as e:
        queue.put(("Error",str(e),None))

def solve_k_with_timeout(total_num, total_adj, k , timeout_sec, solver_name = "glucose3"):
    t0_encoding = time.time()
    clauses, nv = build_cnf(total_num, total_adj, k)
    t_encoding = time.time() - t0_encoding

    ctx = mp.get_context("spawn")
    q = ctx.Queue()
    p = ctx.Process(target=solver_worker, args=(clauses, nv, solver_name, q))
    p.start()

    t0_solving = time.time()
    p.join(timeout_sec)
    t_solving = time.time() - t0_solving

    if p.is_alive():
        p.terminate()
        p.join()
        return "TIMEOUT", None, t_encoding, t_solving, len(clauses), nv
    
    if not q.empty():
        tag, sat, model = q.get()
        if tag == "Done":
            return ("SAT" if sat else "UNSAT"), model, t_encoding, t_solving, len(clauses), nv
        else:
            return "ERROR", None, t_encoding, t_solving, len(clauses), nv
        
    return "TIMEOUT", None, t_encoding, t_solving, len(clauses), nv

def find_total_chromatic_number(adj, timeout_sec = 1800, max_extra = 4, verbose = True, solver_name="glucose3"):
    total_num, total_adj, delta, num_v, num_e = build_total_graph(adj)
    lower_bound = delta + 1

    history = []
    chi_T = None
    final_status = "timeout"
    span_value = None
    t_encoding_total = 0.0
    t_solving_total = 0.0
    vars_count = 0
    clauses_count = 0
    last_sat_k = None

    for k in [lower_bound + 1, lower_bound]:
        t0 = time.time()
        status, model, enc_time, solve_time, clauses_num, vars_num = solve_k_with_timeout(total_num, total_adj, k, timeout_sec, solver_name)
        dt = time.time() - t0
        t_encoding_total += enc_time
        t_solving_total += solve_time
        vars_count = vars_num
        clauses_count = clauses_num
        history.append({"k":k, "status": status, "time_sec":round(dt, 2)})
        if verbose:
            print(f" k={k:>3} -> {status:<8} ({dt:8.2f}s)")

        if status == "SAT":
            last_sat_k = k
            if k == lower_bound:
                chi_T = k
                final_status = "optimal"
                break
            continue

        elif status == "UNSAT":
            if last_sat_k is not None:
                chi_T = last_sat_k
                final_status = "optimal"
            break

        elif status in ("TIMEOUT", "ERROR"):
            final_status = "timeout"
            chi_T = last_sat_k if last_sat_k is not None else None
            break

    return {
            "n": num_v,
            "m": num_e,
            "delta": delta,
            "chi_T": chi_T,
            "vars": vars_count,
            "clauses": clauses_count,
            "t_encoding_sec": round(t_encoding_total, 2),
            "t_solving_sec": round(t_solving_total, 2),
            "t_total_sec": round(t_encoding_total + t_solving_total, 2),
            "status": final_status,
            "span": last_sat_k if last_sat_k is not None else "UNKNOWN",
            "history": history,
        }


def run_batch(data_dir, timeout_sec, out_csv, solver_name="glucose3"):
    supported_exts = (".lst", ".txt")
    files = []
    for ext in supported_exts:
        files.extend(glob.glob(os.path.join(data_dir, f"*{ext}")))
    files = sorted(files)
    if not files:
        print(f"Khong tim thay file do thi (.lst/.txt) nao trong: {data_dir}")
        return 
    
    fieldnames = ["instance_name", "|V|", "|E|", "vars", "clauses", "t_encoding", "t_solving", "t_total", "status", "span", "delta", "chi_T"]
    rows = []
    
    for path in files:
        name = os.path.splitext(os.path.basename(path))[0]
        print(f"\n==={name}===")
        adj = read_file_graph(path)
        if not adj:
            print("(file rong, khong co data)")
            continue

        t_start = time.time()
        result = find_total_chromatic_number(adj, timeout_sec=timeout_sec, solver_name=solver_name)
        total_time = time.time() - t_start

        row = {
            "instance_name": name,
            "|V|": result["n"],
            "|E|": result["m"],
            "vars": result["vars"],
            "clauses": result["clauses"],
            "t_encoding": result["t_encoding_sec"],
            "t_solving": result["t_solving_sec"],
            "t_total": round(total_time, 2),
            "status": result["status"],
            "span": result["span"],
            "delta": result["delta"],
            "chi_T": result["chi_T"] if result["chi_T"] is not None else "UNKNOWN",
        }
        rows.append(row)

        print(f" => {name}: status={row['status']}, span={row['span']}, delta = {result['delta']}, chi_T={result['chi_T']}, t_total={row['t_total']:.2f}s")

        parent_dir = os.path.dirname(out_csv)
        if parent_dir:
            os.makedirs(parent_dir, exist_ok=True)

        with open(out_csv, "w", newline="", encoding = "utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(rows)

    print(f"\nDa ghi ket qua vao: {out_csv}")


def main():
    parser = argparse.ArgumentParser(
        description="Tim so mau nho nhat cho Total Coloring bang SAT (CNF order encoding)."
    )
    parser.add_argument(
        "--data-dir", required=True,
        help="Thu muc chua cac file do thi dang .lst hoac .txt (danh sach ke, 1-indexed)."
    )
    parser.add_argument(
        "--timeout", type=int, default=1800,
        help="Thoi gian toi da (giay) cho MOI lan goi SAT solver. Mac dinh 1800s = 30 phut."
    )
    parser.add_argument(
        "--out", default=None,
        help="File CSV de ghi ket qua. Mac dinh: total_coloring_results_<timestamp>.csv"
    )
    parser.add_argument(
        "--solver", default="glucose3",
        help="Ten SAT solver backend cua pysat (glucose3, glucose4, cadical153, "
             "minisat22, lingeling, ...). Mac dinh: glucose4."
    )
    args = parser.parse_args()

    out_csv = args.out or f"total_coloring_results_{datetime.now():%Y%m%d_%H%M%S}.csv"
    run_batch(args.data_dir, args.timeout, out_csv, solver_name=args.solver)


if __name__ == "__main__":
    main()

