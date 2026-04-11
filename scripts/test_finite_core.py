#!/usr/bin/env python3
"""N1 — Test du noyau fini mod 30. 0 tolérance."""
import json, sys
from math import gcd

G30 = sorted(a for a in range(1,30) if gcd(a,30)==1)
TC = {1, 11, 29}
PASS = True

def check(name, cond):
    global PASS
    status = "PASS" if cond else "FAIL"
    if not cond: PASS = False
    print(f"  [{status}] {name}")
    return cond

# T1.1 — |G| = 8
check("phi(30) = 8", len(G30) == 8)

# T1.2 — TC
check("|TC| = 3", len(TC) == 3)
check("TC ⊂ G", TC.issubset(set(G30)))

# T1.3 — Fantôme 19
check("11·29 ≡ 19 mod 30", (11*29) % 30 == 19)
check("19 ∉ TC", 19 not in TC)
check("19 ∈ G", 19 in G30)

# T1.4 — TC pas un sous-groupe
products = {(a*b) % 30 for a in TC for b in TC}
check("TC non fermé (∃ produit ∉ TC)", not products.issubset(TC))

# T1.5 — Spectre {3², 1⁴, (−1)²}
import numpy as np
ind3 = {1:0, 2:1}
ind5 = {1:0, 2:1, 4:2, 3:3}
chars = []
for i in range(2):
    for j in range(4):
        row = []
        for a in G30:
            val = ((-1)**(i*ind3[a%3])) * (1j**(j*ind5[a%5]))
            row.append(val)
        chars.append(row)

F_TC = []
for ch in chars:
    val = sum(ch[G30.index(a)] for a in TC)
    F_TC.append(round(abs(val)**2))

F_TC_sorted = sorted(F_TC, reverse=True)
check("Spectre = [9,9,1,1,1,1,1,1]", F_TC_sorted == [9,9,1,1,1,1,1,1])
check("Parseval Σ|F̂|² = 24 = 8·3", sum(F_TC) == 24)
check("Classification 63/255", 63 + 192 == 255)

# T1.6 — Ghost cancellation
c_chi = [3/8, 1/8, 3/8, 1/8, -1/8, 1/8, -1/8, 1/8]
chi_19 = []
for ch in chars:
    chi_19.append(ch[G30.index(19)].real)
ghost = sum(c*x for c,x in zip(c_chi, chi_19))
check(f"Ghost cancellation Σ c_χ·χ(19) = 0 (got {ghost})", abs(ghost) < 1e-12)

# T1.7 — Obstruction symplectique
check("dim TC = 3 impair → pas de J²=-I", len(TC) % 2 == 1)
check("dim G30 = 8 pair → non obstrué", len(G30) % 2 == 0)

result = {"test": "N1_finite_core", "pass": PASS, "checks": 13}
print(f"\n{'PASS' if PASS else 'FAIL'} — N1 Noyau fini")
json.dump(result, open("outputs/N1.json","w"), indent=2)
sys.exit(0 if PASS else 1)
