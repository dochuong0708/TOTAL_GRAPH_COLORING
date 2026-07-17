from pysat.solvers import Solver

# Read the graph from a file

def read_graph_from_file(file_path):

    adj = {}
    with open(file_path, "r", encoding = "utf-8") as f:
        for line in f:
            if line.startswith("c"):
                continue
            elif line.startswith("p"):
                _, _, num_vertices, num_edges = line.split()
                num_vertices = int(num_vertices)
                num_edges = int(num_edges)
            else:
                u, v = map(int, line.split())
                if u not in adj:
                    adj[u] = []
                if v not in adj:
                    adj[v] = []
                adj[u].append(v)
                adj[v].append(u)

    return adj
def total_graph_coloring(adj, num_colors):
    num_vertices = len(adj)
    num_edges = sum(len(neighbors) for neighbors in adj.values()) // 2

    # Create a SAT solver instance
    solver = Solver(name='g3')

    # Create variables for vertex colors and edge colors
    vertex_vars = {}
    edge_vars = {}

    for v in range(1, num_vertices + 1):
        for c in range(1, num_colors + 1):
            vertex_vars[(v, c)] = solver.new_var()

    edge_index = 0
    for u in adj:
        for v in adj[u]:
            if u < v:  # To avoid duplicate edges
                edge_index += 1
                for c in range(1, num_colors + 1):
                    edge_vars[(edge_index, c)] = solver.new_var()

    # Add constraints to ensure that adjacent vertices have different colors
    for u in adj:
        for v in adj[u]:
            if u < v:  # To avoid duplicate edges
                for c in range(1, num_colors + 1):
                    solver.add_clause([-vertex_vars[(u, c)], -vertex_vars[(v, c)]])

    # Add constraints to ensure that adjacent edges have different colors
    edge_list = list(edge_vars.keys())
    for i in range(len(edge_list)):
        for j in range(i + 1, len(edge_list)):
            e1, e2 = edge_list[i], edge_list[j]
            if (e1[0] == e2[0]) or (e1[0] == e2[1]) or (e1[1] == e2[0]) or (e1[1] == e2[1]):
                for c in range(1, num_colors + 1):
                    solver.add_clause([-edge_vars[e1], -edge_vars[e2]])

    # Add constraints to ensure that each vertex has at least one color
    for v in range(1, num_vertices + 1):
        solver.add_clause([vertex_vars[(v, c)] for c in range(1, num_colors + 1)])

    # Add constraints to ensure that each edge has at least one color
    for e in edge_list:
        solver.add_clause([edge_vars[e] for c in range(1, num_colors + 1)])

    # Solve the SAT problem
    if solver.solve():
        model = solver.get_model()
        vertex_colors = {}
        edge_colors = {}

        for v in range(1, num_vertices + 1):
            for c in range(1, num_colors + 1):
                if model[vertex_vars[(v, c)] - 1] > 0:
                    vertex_colors[v] = c
                    break

        for e in edge_list:
            for c in range(1, num_colors + 1):
                if model[edge_vars[e] - 1] > 0:
                    edge_colors[e] = c
                    break

        return vertex_colors, edge_colors
def main():
    file_path = ""  # Replace with your graph file path
    num_colors = 3  # Replace with the desired number of colors

    adj = read_graph_from_file(file_path)
    vertex_colors, edge_colors = total_graph_coloring(adj, num_colors)

    print("Vertex Colors:")
    for v in vertex_colors:
        print(f"Vertex {v}: Color {vertex_colors[v]}")

    print("\nEdge Colors:")
    for e in edge_colors:
        print(f"Edge {e}: Color {edge_colors[e]}")