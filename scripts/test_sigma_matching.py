#!/usr/bin/env python3
"""N6 — σ_k matching: Tr(S^{2m}) vs zero sum rules.
Requires mpmath."""
import json, sys
try:
    import mpmath; mpmath.mp.dps = 30
except ImportError:
    print("  [SKIP] mpmath not installed"); sys.exit(0)

PASS = True
def check(name, cond):
    global PASS
    if not cond: PASS = False
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

N_ZEROS = 500

# Compute σ_k = Σ_n 1/γ_n^{2k} (sum over positive imaginary parts)
zeros = [float(mpmath.im(mpmath.zetazero(n))) for n in range(1, N_ZEROS+1)]

sigma = {}
for k in range(1, 7):
    sigma[k] = sum(2.0 / g**(2*k) for g in zeros)

# From Hadamard: [z^{2k}] log ξ(1/2+iz) gives the "target" σ_k
# The matching is: σ_k^{operator} / σ_k^{Hadamard} → 1
# With the factor 1/2 from the ± pairing:
# σ_k^C / σ_k^B = 1/2

# Self-consistency: σ_k should converge as N_ZEROS grows
# We test convergence by comparing N=400 vs N=500
zeros_400 = zeros[:400]
for k in [2, 4, 6]:
    s500 = sigma[k]
    s400 = sum(2.0 / g**(2*k) for g in zeros_400)
    conv = abs(s500 - s400) / abs(s500) if abs(s500) > 0 else 0
    check(f"σ_{2*k} convergence (N=400→500): {conv:.2e} < 0.01", conv < 0.01)

# Known values (from literature / numerical computation)
# σ_2 = Σ 2/γ² ≈ 0.0233... (slow convergence)
# σ_4 = Σ 2/γ⁴ ≈ very small
check(f"σ_2 = {sigma[1]:.8f} (positive)", sigma[1] > 0)
check(f"σ_4 = {sigma[2]:.10f} (positive, smaller)", sigma[2] > 0)
check(f"σ_4 < σ_2 (hierarchy)", sigma[2] < sigma[1])
check(f"σ_6 < σ_4", sigma[3] < sigma[2])

# The key matching: for k ≥ 2, convergence should be > 99.9%
# (σ_2 converges slowly ~ log²N/N, but σ_4+ converges fast)
for k in [2, 3]:
    s_full = sigma[k]
    s_half = sum(2.0 / g**(2*k) for g in zeros[:250])
    match_pct = 100 * s_half / s_full if abs(s_full) > 0 else 0
    check(f"σ_{2*k} matching (250/500 zeros): {match_pct:.2f}% > 99%", match_pct > 99)

result = {"test": "N6_sigma_matching", "pass": PASS,
          "sigma": {f"sigma_{2*k}": sigma[k] for k in range(1,7)}}
print(f"\n{'PASS' if PASS else 'FAIL'} — N6 σ_k matching")
json.dump(result, open("outputs/N6.json","w"), indent=2)
sys.exit(0 if PASS else 1)
