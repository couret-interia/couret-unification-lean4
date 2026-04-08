#!/usr/bin/env python3
"""PACK THOMAS — V_eff (fast vectorized version)"""
import numpy as np
import mpmath

print("=" * 60)
print("  PACK THOMAS — V_eff (fast)")
print("=" * 60)

# ── V(ζ) ──
V_zeta = 0.0
for n in range(1, 201):
    g = float(mpmath.zetazero(n).imag)
    V_zeta += 2.0 / (0.25 + g**2)
print(f"\nV(ζ) = {V_zeta:.10f}  (200 zeros)")

# ── Fast L-function eval using numpy ──
def make_L_evaluator(chi_vals_mod_q, q, N=5000):
    """Return function that evaluates Re(L(1/2+it)) fast."""
    ns = np.arange(1, N+1)
    chi_arr = np.array([chi_vals_mod_q[n % q] for n in ns])
    mask = chi_arr != 0
    ns_m = ns[mask].astype(float)
    chi_m = chi_arr[mask].astype(complex)
    log_ns = np.log(ns_m)
    mag = ns_m ** (-0.5)
    
    def eval_L(t):
        phases = np.exp(-1j * t * log_ns)
        val = np.sum(chi_m * mag * phases)
        return val.real, val.imag
    return eval_L

def find_zeros_fast(eval_L, T_max=200, dt=0.1):
    zeros = []
    t = 0.5
    prev_re, _ = eval_L(t)
    while t < T_max:
        t += dt
        cur_re, _ = eval_L(t)
        if prev_re * cur_re < 0:
            a, b = t - dt, t
            for _ in range(35):
                m = (a+b)/2
                v, _ = eval_L(m)
                if eval_L(a)[0] * v < 0: b = m
                else: a = m
            zeros.append((a+b)/2)
        prev_re = cur_re
    return zeros

def V_sum(zeros):
    return sum(2.0/(0.25+g**2) for g in zeros)

# ── Character tables ──
# chi_{-3} (Legendre mod 3): {0:0, 1:1, 2:-1}
chi3 = {0:0, 1:1, 2:-1}

# chi_5 (Legendre mod 5): QR={1,4}, NR={2,3}
chi5L = {0:0, 1:1, 2:-1, 3:-1, 4:1}

# chi_5 order 4: chi(1)=1, chi(2)=i, chi(3)=-i, chi(4)=-1
chi5o4 = {0:0, 1:1, 2:1j, 3:-1j, 4:-1}

# chi_{-15} = chi3 * chi5L
chi15r = {}
for n in range(15):
    chi15r[n] = chi3[n%3] * chi5L[n%5] if (n%3!=0 and n%5!=0) else 0

# chi_15_cpx = chi3 * chi5o4
chi15c = {}
for n in range(15):
    chi15c[n] = chi3[n%3] * chi5o4[n%5] if (n%3!=0 and n%5!=0) else 0

# ── Compute zeros ──
T_MAX = 200
print(f"\nScanning zeros up to T={T_MAX}...\n")

print("  χ₃ (cond 3)...", end=" ", flush=True)
L3 = make_L_evaluator(chi3, 3)
z3 = find_zeros_fast(L3, T_MAX)
V3 = V_sum(z3)
print(f"{len(z3)} zeros, V = {V3:.8f}")

print("  χ₅L (cond 5)...", end=" ", flush=True)
L5 = make_L_evaluator(chi5L, 5)
z5 = find_zeros_fast(L5, T_MAX)
V5 = V_sum(z5)
print(f"{len(z5)} zeros, V = {V5:.8f}")

print("  χ₅o4 (cond 5, cpx)...", end=" ", flush=True)
L5c = make_L_evaluator(chi5o4, 5)
z5c = find_zeros_fast(L5c, T_MAX)
V5c = V_sum(z5c)
print(f"{len(z5c)} zeros, V = {V5c:.8f}")

print("  χ₁₅r (cond 15)...", end=" ", flush=True)
L15r = make_L_evaluator(chi15r, 15)
z15r = find_zeros_fast(L15r, T_MAX)
V15r = V_sum(z15r)
print(f"{len(z15r)} zeros, V = {V15r:.8f}")

print("  χ₁₅c (cond 15, cpx)...", end=" ", flush=True)
L15c = make_L_evaluator(chi15c, 15)
z15c = find_zeros_fast(L15c, T_MAX)
V15c = V_sum(z15c)
print(f"{len(z15c)} zeros, V = {V15c:.8f}")

# ── Assemblage ──
print(f"\n{'═'*60}")
V_eff = (9/64)*V_zeta + (9/64)*V5 + (1/64)*V3 + (1/64)*V15r + (2/64)*V5c + (2/64)*V15c

print(f"  (9/64)×V(ζ)     = {(9/64)*V_zeta:.10f}")
print(f"  (9/64)×V(χ₅L)   = {(9/64)*V5:.10f}")
print(f"  (1/64)×V(χ₃)    = {(1/64)*V3:.10f}")
print(f"  (1/64)×V(χ₁₅r)  = {(1/64)*V15r:.10f}")
print(f"  (2/64)×V(χ₅o4)  = {(2/64)*V5c:.10f}")
print(f"  (2/64)×V(χ₁₅c)  = {(2/64)*V15c:.10f}")

print(f"\n  V_eff     = {V_eff:.10f}")
print(f"  1/7       = {1/7:.10f}")
print(f"  RATIO     = {V_eff*7:.6f}")
print(f"  √V_eff    = {V_eff**0.5:.10f}")
print(f"  1/√7      = {7**(-0.5):.10f}")
print(f"{'═'*60}")

if abs(V_eff*7 - 1) < 0.05:
    print("  ✅ V_eff ≈ 1/7 — mécanisme analytique !")
elif abs(V_eff*7 - 1) < 0.15:
    print("  ⚠️ Zone ambiguë")
else:
    print("  ❌ V_eff ≠ 1/7 — coïncidence numérique")

print(f"\n  Parseval: {9/64+9/64+1/64+1/64+2/64+2/64} = {3/8}")
print(f"  RHClaimed = false")
