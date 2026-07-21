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
            head, _, rest = line.partition(":")
            u = int(head.strip())
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
    clauses, nv = build_cnf(total_num, total_adj, k)

    ctx = mp.get_context("spawn")
    q = ctx.Queue()
    p = ctx.Process(target=solver_worker, args=(clauses, nv, solver_name, q))
    p.start()
    p.join(timeout_sec)

    if p.is_alive():
        p.terminate()
        p.join()
        return "TIMEOUT", None
    
    if not q.empty():
        tag, sat, model = q.get()
        if tag == "Done":
            return ("SAT" if sat else "UNSAT"), model
        else:
            return "ERROR", None
        
    return "TIMEOUT", None

def find_total_chromatic_number(adj, timeout_sec = 1800, max_extra = 4, verbose = True, solver_name="glucose3"):
    total_num, total_adj, delta, num_v, num_e = build_total_graph(adj)
    lower_bound = delta + 1

    history = []
    chi_T = None
    for k in range(lower_bound, lower_bound + max_extra + 1):
        t0 = time.time()
        status, model = solve_k_with_timeout(total_num, total_adj, k, timeout_sec, solver_name)
        dt = time.time() - t0
        history.append({"k":k, "status": status, "time_sec":round(dt, 2)})
        if verbose:
            print(f" k={k:>3} -> {status:<8} ({dt:8.2f}s)")
        if status == "SAT":
            chi_T = k
            break
        if status in ("TIMEOUT", "ERROR"):
            break

    return {
            "n": num_v,
            "m": num_e,
            "delta": delta,
            "chi_T": chi_T,
            "history": history,
        }


def run_batch(data_dir, timeout_sec, out_csv, solver_name="glucose3"):
    files = sorted(glob.glob(os.path.join(data_dir, "*.lst")))
    if not files:
        print(f"Khong tim thay file .list nao trong: {data_dir}")
        return 
    
    fieldnames = ["graph", "n", "m", "delta", "chi_T", "total_time_sec", "detail"]
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

        detail = "; ".join(
            f"k={h['k']}:{h['status']}({h['time_sec']}s)" for h in result["history"]
        )

        row = {
            "graph": name,
            "n": result["n"],
            "m": result["m"],
            "delta": result["delta"],
            "chi_T": result["chi_T"] if result["chi_T"] is not None else "UNKNOWN",
            "total_time_sec": round(total_time, 2),
            "detail": detail,
        }
        rows.append(row)

        print(f" => chi_T({name}) = {row['chi_T']}  (tong thoi gian: {total_time:.2f}s))")

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
        help="Thu muc chua cac file do thi dang .lst (danh sach ke, 1-indexed)."
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

