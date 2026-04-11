#!/usr/bin/env python3
"""
Couret-Defect Numerical Laboratory
===================================
Computes the absorption ratio R(L,T) = E_arch(L,T) / Z_tot(L,T)
for the two quadratic defect channels chi_3 and chi_15 (mod 30).

Uses a Gaussian windowed positive test family:
  phi_{L,T}  with  hat{phi}(1/2+it) ~ L * exp(-L^2(t-T)^2)

Zeros of L(s,chi) computed via mpmath.
"""

import math
import numpy as np
from scipy.integrate import quad
from scipy.special import digamma as scipy_digamma
import mpmath
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

# ============================================================
# 1. Channel data
# ============================================================
# chi_3: the non-trivial character mod 3  (conductor 3, even => kappa=0)
# chi_15: identify with the non-trivial real character mod 15
#   that pairs with chi_3 in the defect sector E_-.
#   For numerical purposes we use conductor 15, kappa=0 (even).
#   NOTE: exact identification may need refinement.

CHANNELS = {
    "chi3":  {"q": 3,  "kappa": 0},
    "chi15": {"q": 15, "kappa": 0},
}

# ============================================================
# 2. Compute zeros of L(s, chi) via mpmath
# ============================================================
def make_chi_values(q, chi_dict):
    """Return a function chi(n) from a dict {residue: value}."""
    def chi(n):
        r = n % q
        return chi_dict.get(r, 0)
    return chi

# chi_3: the non-trivial character mod 3: chi(1)=1, chi(2)=-1, chi(0)=0
CHI3_VALS = {1: 1, 2: -1}
# chi_15: Jacobi symbol (n/15) — a real non-principal character mod 15
#   (Z/15Z)* = {1,2,4,7,8,11,13,14}
#   Jacobi(n,15) = Legendre(n,3)*Legendre(n,5)
CHI15_VALS = {1:1, 2:1, 4:1, 7:-1, 8:-1, 11:-1, 13:-1, 14:1}


def L_crit_line_real(t, chi_func, q, n_terms=8000):
    """Evaluate Re(L(1/2+it, chi)) using numpy for speed."""
    ns = np.arange(1, n_terms + 1)
    chi_vals = np.array([chi_func(int(n)) for n in ns])
    mask = chi_vals != 0
    ns = ns[mask]
    chi_vals = chi_vals[mask]
    mag = ns ** (-0.5)
    ln_ns = np.log(ns)
    re_part = np.sum(chi_vals * mag * np.cos(t * ln_ns))
    return re_part


def find_zeros_on_crit(chi_func, q, n_zeros=60, t_max=200):
    """Find zeros by scanning sign changes of Re(L(1/2+it, chi))."""
    print(f"  Scanning for zeros of L(s, chi) mod {q}...")
    dt = 0.25
    t = 0.3
    re_prev = L_crit_line_real(t, chi_func, q)
    found = []

    while len(found) < n_zeros and t < t_max:
        t += dt
        re_cur = L_crit_line_real(t, chi_func, q)
        if re_prev * re_cur < 0:
            a, b = t - dt, t
            va = re_prev
            for _ in range(40):
                mid = (a + b) / 2
                vm = L_crit_line_real(mid, chi_func, q)
                if va * vm < 0:
                    b = mid
                else:
                    a = mid
                    va = vm
            gamma = (a + b) / 2
            found.append(gamma)
        re_prev = re_cur

    print(f"    Found {len(found)} zeros (max gamma ~ {found[-1]:.2f})" if found else "    WARNING: No zeros found!")
    return found


def get_zeros():
    """Get zeros for both channels."""
    print("Computing Dirichlet L-function zeros on critical line...")

    chi3 = make_chi_values(3, CHI3_VALS)
    chi15 = make_chi_values(15, CHI15_VALS)

    z3 = find_zeros_on_crit(chi3, 3, n_zeros=60)
    z15 = find_zeros_on_crit(chi15, 15, n_zeros=60)

    return {"chi3": z3, "chi15": z15}


# ============================================================
# 3. Spectral weight (Gaussian kernel)
# ============================================================
def h_hat(u):
    """Fourier transform of Gaussian h(x) = exp(-x^2/2): h_hat(u) = exp(-u^2/2)."""
    return np.exp(-0.5 * np.asarray(u)**2)


def Z_channel(L, T, gammas):
    """Positive spectral mass for one channel:
       sum_j  L^2 |h_hat(L(gamma_j - T))|^4
    """
    g = np.array(gammas)
    w = h_hat(L * (g - T))
    return np.sum(L**2 * w**4)


def Z_total(L, T, zeros):
    """Total spectral mass = (1/8) sum over channels."""
    return (1.0 / 8.0) * sum(Z_channel(L, T, zeros[ch]) for ch in zeros)


# ============================================================
# 4. Archimedean term
# ============================================================
def G_chi(t, q, kappa):
    """Archimedean kernel:
       G_chi(t) = (1/2) log(q/pi) + (1/2) Re psi((1/2 + kappa + it)/2)
    """
    z = complex(0.5 + kappa, t) / 2.0
    # scipy digamma accepts complex
    return 0.5 * math.log(q / math.pi) + 0.5 * scipy_digamma(z).real


def archimedean_channel(L, T, q, kappa):
    """Numerical integral:
       (1/2pi) int G_chi(T + u/L) |h_hat(u)|^2 du
    """
    def integrand(u):
        return G_chi(T + u / L, q, kappa) * math.exp(-u * u)  # |h_hat(u)|^2 = exp(-u^2)
    res, _ = quad(integrand, -10, 10, limit=200)
    return res / (2 * math.pi)


def E_arch(L, T):
    """Total archimedean remainder = (1/8) sum |A_chi|."""
    total = 0.0
    for ch, p in CHANNELS.items():
        total += abs(archimedean_channel(L, T, p["q"], p["kappa"]))
    return total / 8.0


# ============================================================
# 5. Absorption ratio
# ============================================================
def absorption_ratio(L, T, zeros):
    zt = Z_total(L, T, zeros)
    if zt <= 1e-30:
        return float("inf")
    return E_arch(L, T) / zt


# ============================================================
# 6. Grid scan and plotting
# ============================================================
def scan_and_plot(zeros):
    L_vals = np.linspace(0.2, 4.0, 30)
    T_vals = np.linspace(2.0, 50.0, 40)

    print(f"\nScanning {len(L_vals)}x{len(T_vals)} = {len(L_vals)*len(T_vals)} grid points...")

    R_grid = np.full((len(T_vals), len(L_vals)), np.nan)

    for i, T in enumerate(T_vals):
        for j, L in enumerate(L_vals):
            r = absorption_ratio(L, T, zeros)
            R_grid[i, j] = min(r, 5.0)  # cap for display
        if (i + 1) % 10 == 0:
            print(f"  Row {i+1}/{len(T_vals)} done")

    # Count absorbing points
    absorbing = np.sum(R_grid < 1.0)
    total = R_grid.size
    print(f"\nAbsorbing points (R < 1): {absorbing}/{total} = {100*absorbing/total:.1f}%")

    # --- Heatmap ---
    fig, ax = plt.subplots(figsize=(10, 7))
    im = ax.pcolormesh(L_vals, T_vals, R_grid, cmap="RdYlGn_r", vmin=0, vmax=3, shading="auto")
    cb = fig.colorbar(im, ax=ax, label=r"$\mathfrak{R}(L,T)$")
    ax.contour(L_vals, T_vals, R_grid, levels=[1.0], colors="black", linewidths=2)
    ax.set_xlabel("L (résolution spectrale)")
    ax.set_ylabel("T (hauteur spectrale)")
    ax.set_title("Carte d'absorption — Critère Couret-défaut\n"
                  r"$\mathfrak{R}(L,T) < 1$ ⟹ absorption (vert)")
    fig.tight_layout()
    fig.savefig("../outputs/absorption_map.png", dpi=150)
    print("Heatmap saved: absorption_map.png")

    # --- Slice at best T ---
    best_T_idx = np.argmin(np.min(R_grid, axis=1))
    best_T = T_vals[best_T_idx]
    fig2, ax2 = plt.subplots(figsize=(8, 4))
    ax2.plot(L_vals, R_grid[best_T_idx, :], "b-o", markersize=3)
    ax2.axhline(1.0, color="red", linestyle="--", label="R = 1 (seuil)")
    ax2.set_xlabel("L")
    ax2.set_ylabel(r"$\mathfrak{R}(L,T)$")
    ax2.set_title(f"Coupe à T = {best_T:.1f} (meilleure hauteur)")
    ax2.legend()
    ax2.set_ylim(0, 4)
    fig2.tight_layout()
    fig2.savefig("../outputs/absorption_slice.png", dpi=150)
    print("Slice saved: absorption_slice.png")

    # --- Print summary table ---
    print(f"\n{'L':>6} {'T':>8} {'Z_tot':>12} {'E_arch':>12} {'R':>8} {'Absorb':>8}")
    print("-" * 60)
    sample_Ls = [0.5, 1.0, 2.0, 3.0]
    sample_Ts = [5.0, 14.0, 25.0, 40.0]
    for T in sample_Ts:
        for L in sample_Ls:
            zt = Z_total(L, T, zeros)
            ea = E_arch(L, T)
            r = ea / zt if zt > 1e-30 else float("inf")
            absorb = "YES" if r < 1 else "no"
            print(f"{L:6.2f} {T:8.2f} {zt:12.6e} {ea:12.6e} {r:8.4f} {absorb:>8}")


# ============================================================
# Main
# ============================================================
if __name__ == "__main__":
    zeros = get_zeros()
    scan_and_plot(zeros)
