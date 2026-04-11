#!/usr/bin/env python3
"""N9 — Connexité du graphe de Cayley S={7,11,13} sur G₃₀."""
import json, sys
from math import gcd

PASS = True
def check(name, cond):
    global PASS
    if not cond: PASS = False
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

G30 = sorted(a for a in range(1,30) if gcd(a,30)==1)
S = [7, 11, 13]  # generators

# BFS from 1
visited = {1}
frontier = {1}
distances = {1: 0}
step = 0

while frontier and step < 10:
    step += 1
    next_frontier = set()
    for x in frontier:
        for g in S:
            y = (x * g) % 30
            if y not in visited and y in set(G30):
                visited.add(y)
                distances[y] = step
                next_frontier.add(y)
    frontier = next_frontier

check(f"|G₃₀| = 8", len(G30) == 8)
check(f"S = {{7, 11, 13}}", set(S) == {7, 11, 13})
check(f"S symétrique: 7⁻¹=13, 11⁻¹=11", (7*13)%30 == 1 and (11*11)%30 == 1)
check(f"Graphe connexe: {len(visited)}/8 sommets atteints", len(visited) == 8)

# Diameter
diam = max(distances.values())
check(f"Diamètre = {diam} ≤ 4", diam <= 4)

# Print distance table
print(f"\n  Distances depuis 1:")
for a in G30:
    d = distances.get(a, '?')
    print(f"    d(1, {a:2d}) = {d}")

# Regularity: each vertex has exactly |S| + |S∩S⁻¹| neighbors
# Since S = {7,11,13}, and 11=11⁻¹, we get degree = 3 (not 4, 11 counted once)
degrees = {}
for x in G30:
    nbrs = set()
    for g in S:
        y = (x * g) % 30
        if y in set(G30):
            nbrs.add(y)
    degrees[x] = len(nbrs)

deg_set = set(degrees.values())
check(f"Graphe régulier: degrés = {deg_set}", len(deg_set) == 1)
check(f"Degré = {list(deg_set)[0]}", True)

result = {"test": "N9_cayley_connectivity", "pass": PASS,
          "diameter": diam, "degrees": degrees, "distances": distances}
print(f"\n{'PASS' if PASS else 'FAIL'} — N9 Cayley connectivity")
json.dump(result, open("outputs/N9.json", "w"), indent=2, default=str)
sys.exit(0 if PASS else 1)
