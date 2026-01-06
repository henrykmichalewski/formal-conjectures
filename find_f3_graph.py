
import networkx as nx
from itertools import combinations

def find_graph():
    n = 7
    for edges in combinations(combinations(range(n), 2), 8): # Try 8 edges
        G = nx.Graph(edges)
        if not nx.is_connected(G): continue
        if nx.clique_number(G) > 2: continue
        if nx.chromatic_number(G) != 3: continue

        degrees = [d for n, d in G.degree()]
        freqs = {}
        for d in degrees:
            freqs[d] = freqs.get(d, 0) + 1

        if max(freqs.values()) == 3:
            print(f"Found graph with 8 edges: {edges}")
            print(f"Degrees: {degrees}")
            return G

    for edges in combinations(combinations(range(n), 2), 9): # Try 9 edges
        G = nx.Graph(edges)
        if not nx.is_connected(G): continue
        if nx.clique_number(G) > 2: continue
        if nx.chromatic_number(G) != 3: continue

        degrees = [d for n, d in G.degree()]
        freqs = {}
        for d in degrees:
            freqs[d] = freqs.get(d, 0) + 1

        if max(freqs.values()) == 3:
            print(f"Found graph with 9 edges: {edges}")
            print(f"Degrees: {degrees}")
            return G

    for edges in combinations(combinations(range(n), 2), 10): # Try 10 edges
        G = nx.Graph(edges)
        if not nx.is_connected(G): continue
        if nx.clique_number(G) > 2: continue
        if nx.chromatic_number(G) != 3: continue

        degrees = [d for n, d in G.degree()]
        freqs = {}
        for d in degrees:
            freqs[d] = freqs.get(d, 0) + 1

        if max(freqs.values()) == 3:
            print(f"Found graph with 10 edges: {edges}")
            print(f"Degrees: {degrees}")
            return G

if __name__ == "__main__":
    find_graph()
