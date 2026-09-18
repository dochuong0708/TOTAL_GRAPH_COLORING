from collections import defaultdict

def parse_dimacs_to_adj_list(input_file, output_file):
    adj = defaultdict(set)
    num_vertices = 0

    with open(input_file, "r") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("c"):
                continue
            parts = line.split()
            if parts[0] == "p":
                num_vertices = int(parts[2])
            elif parts[0] == "e":
                u, v = int(parts[1]), int(parts[2])
                adj[u].add(v)
                adj[v].add(u)

    with open(output_file, "w") as f:
        for u in range(1, num_vertices + 1):
            neighbors = sorted(list(adj[u]))
            neighbors_str = " ".join(map(str, neighbors))
            f.write(f"{u}: {neighbors_str}\n")