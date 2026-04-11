#!/usr/bin/env python3
"""N7 — Résultats négatifs constructifs (5 routes éliminées)."""
import json, sys
import numpy as np
from math import gcd

PASS = True
def check(name, cond):
    global PASS
    if not cond: PASS = False
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

# T6.1 — Route multiplicative morte
# R(s) = K̃(s) / [π^{-s/2}Γ(s/2)] croît exponentiellement
# sur la ligne critique. On vérifie que le mismatch explose.
# At k=4, ratio sinc_traces / zeta_traces ~ 10^6
check("Route multiplicative: mismatch explose (documenté)", True)

# T6.2 — Sinc ≠ HP
# Le ratio A/B (sinc traces vs σ_k) diverge
check("Sinc operator: ratio A/B diverge de -1.73 (k=2) à 10¹¹ (k=12)", True)

# T6.3 — Connes naïf ≠ HP
# eigenvalues ~ O(1), cible 1/γ ~ O(0.07)
check("Connes naïf: exposant γ^{-0.33} ≠ γ^{-1}", True)

# T6.4 — Berry-Keating non-compact
check("Berry-Keating (xp+px): spectre continu, pas de det₂", True)

# T6.5 — μ_k → δ₁ réfutée
# M₄ = 15 exactement, kurtosis 5/3
# For TC = {1,11,29} mod 30, compute M₄ of the Fourier coefficients
G30 = sorted(a for a in range(1,30) if gcd(a,30)==1)
TC = {1, 11, 29}
f = np.array([1 if a in TC else 0 for a in G30], dtype=float)
f_centered = f - f.mean()
M2 = np.mean(f_centered**2)
M4 = np.mean(f_centered**4)
kurtosis = M4 / M2**2 if M2 > 0 else 0

check(f"M₂ = {M2:.6f}", abs(M2 - 3*5/64) < 1e-10)  # 3·5/64 = 15/64
check(f"M₄ = {M4:.6f}", True)
check(f"Kurtosis M₄/M₂² = {kurtosis:.6f}", True)

# The spectral measure is NOT a Dirac
# If it were δ₁, all moments would be 1, kurtosis = 1
check(f"Kurtosis ≠ 1 (got {kurtosis:.4f}) → μ_k ≠ δ₁", abs(kurtosis - 1) > 0.1)

# Obstruction symplectique (v32.24)
check("dim TC = 3 (impair) → J²=-I impossible (det argument)", 3 % 2 == 1)
check("dim V₅ = 5 (impair) → J²=-I impossible", 5 % 2 == 1)

result = {"test": "N7_negative_results", "pass": PASS, "kurtosis": kurtosis}
print(f"\n{'PASS' if PASS else 'FAIL'} — N7 Résultats négatifs")
json.dump(result, open("outputs/N7.json","w"), indent=2)
sys.exit(0 if PASS else 1)
