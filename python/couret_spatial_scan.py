#!/usr/bin/env python3
"""
couret_spatial_scan.py — Mesure canonique G2 opérateur
Programme Couret-Unification v32.31

Clarification InterIA décisive :
  A_q = K_Q^{prime_scale} ⊗ A_TC
  Ã_q = K_Q ⊗ D,  D = diag(3,3,1,1,1,1,-1,-1)

DEUX COUPURES, DEUX OBJETS :
  - Spectrale (sur U₃₀) : M_RS = M_SR = 0 exactement (D diagonal)
  - Spatiale (sur τ)     : B_21 ≠ 0, c'est ici que vit la fuite

Convention :
  M_RR, M_RS, M_SR, M_SS = coupure spectrale sur U₃₀ (nulle)
  B_11, B_12, B_21, B_22  = coupure spatiale sur T(x)

Factorisation exacte :
  B_21 = K_21 ⊗ D
  ‖B_21‖₂ = 3 · ‖K_21‖₂
  ‖B_21‖_HS = √24 · ‖K_21‖_HS

Usage : python couret_spatial_scan.py

RHClaimed = false
Dédié à Bernard Couret (1928–2010)
"""

import math
import numpy as np
from scipy.sparse import coo_matrix, csr_matrix
from scipy.sparse.linalg import svds
from math import gcd
from functools import reduce

# ═══════════════════════════════════════════════════════════
# §1. Constantes spectrales
# ═══════════════════════════════════════════════════════════

EIGVALS_TC = np.array([3, 3, 1, 1, 1, 1, -1, -1], dtype=float)
D_OP_NORM = float(np.max(np.abs(EIGVALS_TC)))   # 3
D_HS_NORM = float(np.linalg.norm(EIGVALS_TC))   # sqrt(24) ≈ 4.899

# ═══════════════════════════════════════════════════════════
# §2. Normes creuses
# ═══════════════════════════════════════════════════════════

def sparse_op_norm(M: csr_matrix) -> float:
    if min(M.shape) == 0 or M.nnz == 0:
        return 0.0
    if min(M.shape) == 1:
        return float(np.sqrt(np.sum(np.abs(M.data) ** 2)))
    s = svds(M, k=1, return_singular_vectors=False)
    return float(abs(s[0]))

def sparse_hs_norm(M: csr_matrix) -> float:
    if M.nnz == 0:
        return 0.0
    return float(np.sqrt(np.sum(np.abs(M.data) ** 2)))

# ═══════════════════════════════════════════════════════════
# §3. Construction des queues CRT
# ═══════════════════════════════════════════════════════════

def primorial(k):
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    ps = primes[:k]
    q = reduce(lambda a, b: a * b, ps)
    return q, ps

def build_tau_list(q, primes):
    """
    Construit la liste des queues τ pour le primoriel q.
    τ = a // 30 pour a copremier à q, regroupé par résidu mod 30.
    Chaque τ correspond à un unique bloc CRT.
    """
    tail_primes = [p for p in primes if p > 5]
    if not tail_primes:
        return [0]

    Q = reduce(lambda a, b: a * b, tail_primes)
    taus = sorted(set(a % Q for a in range(1, Q + 1) if gcd(a, Q) == 1))
    return taus

# ═══════════════════════════════════════════════════════════
# §4. Blocs K_Q par seuil arithmétique (sans K_Q global)
# ═══════════════════════════════════════════════════════════

def build_blocks_by_threshold(
    tau_list,
    tau_cut: int,
    prime_divisors,
    a0: float = 1.0,
    a1: float = 0.25,
):
    """
    Construit directement K11, K12, K21, K22 pour la coupure
    τ ≤ tau_cut / τ > tau_cut, sans former K_Q global.
    """
    tau_sorted = sorted(set(int(t) for t in tau_list))
    tau_set = set(tau_sorted)

    small_tau = [t for t in tau_sorted if t <= tau_cut]
    large_tau = [t for t in tau_sorted if t > tau_cut]

    pos_small = {t: i for i, t in enumerate(small_tau)}
    pos_large = {t: i for i, t in enumerate(large_tau)}

    rows11, cols11, data11 = [], [], []
    rows12, cols12, data12 = [], [], []
    rows21, cols21, data21 = [], [], []
    rows22, cols22, data22 = [], [], []

    def emit(src_tau: int, dst_tau: int, w: float):
        src_small = src_tau in pos_small
        dst_small = dst_tau in pos_small

        if src_small and dst_small:
            rows11.append(pos_small[dst_tau])
            cols11.append(pos_small[src_tau])
            data11.append(w)
        elif src_small and not dst_small:
            rows21.append(pos_large[dst_tau])
            cols21.append(pos_small[src_tau])
            data21.append(w)
        elif (not src_small) and dst_small:
            rows12.append(pos_small[dst_tau])
            cols12.append(pos_large[src_tau])
            data12.append(w)
        else:
            rows22.append(pos_large[dst_tau])
            cols22.append(pos_large[src_tau])
            data22.append(w)

    for tau in tau_sorted:
        emit(tau, tau, a0)
        for p in prime_divisors:
            tau2 = tau // p
            if tau2 not in tau_set or tau2 == tau:
                continue
            emit(tau, tau2, a1)
            emit(tau2, tau, a1)

    K11 = coo_matrix(
        (data11, (rows11, cols11)), shape=(len(small_tau), len(small_tau))
    ).tocsr()
    K12 = coo_matrix(
        (data12, (rows12, cols12)), shape=(len(small_tau), len(large_tau))
    ).tocsr()
    K21 = coo_matrix(
        (data21, (rows21, cols21)), shape=(len(large_tau), len(small_tau))
    ).tocsr()
    K22 = coo_matrix(
        (data22, (rows22, cols22)), shape=(len(large_tau), len(large_tau))
    ).tocsr()

    return small_tau, large_tau, K11, K12, K21, K22

# ═══════════════════════════════════════════════════════════
# §5. Blocs K_Q par indice (historique, pour comparaison)
# ═══════════════════════════════════════════════════════════

def build_KQ_global(tau_list, prime_divisors, a0=1.0, a1=0.25):
    tau_sorted = sorted(set(int(t) for t in tau_list))
    pos = {t: i for i, t in enumerate(tau_sorted)}
    tau_set = set(tau_sorted)

    rows, cols, data = [], [], []

    for tau in tau_sorted:
        rows.append(pos[tau]); cols.append(pos[tau]); data.append(a0)
        for p in prime_divisors:
            tau2 = tau // p
            if tau2 not in tau_set or tau2 == tau:
                continue
            rows.append(pos[tau2]); cols.append(pos[tau]); data.append(a1)
            rows.append(pos[tau]); cols.append(pos[tau2]); data.append(a1)

    KQ = coo_matrix(
        (data, (rows, cols)),
        shape=(len(tau_sorted), len(tau_sorted)),
    ).tocsr()
    return tau_sorted, KQ

def extract_blocks_by_index(KQ, k):
    n = KQ.shape[0]
    k = max(0, min(k, n))
    small = np.arange(k, dtype=int)
    large = np.arange(k, n, dtype=int)
    return small, large, KQ[small][:, small], KQ[small][:, large], KQ[large][:, small], KQ[large][:, large]

# ═══════════════════════════════════════════════════════════
# §6. Lift des normes K → B
# ═══════════════════════════════════════════════════════════

def lift_block_norms(K11, K12, K21, K22, norm_kind="hs"):
    if norm_kind == "hs":
        c = D_HS_NORM
        nrm = sparse_hs_norm
    elif norm_kind == "op":
        c = D_OP_NORM
        nrm = sparse_op_norm
    else:
        raise ValueError("norm_kind doit valoir 'hs' ou 'op'.")

    B11 = c * nrm(K11)
    B12 = c * nrm(K12)
    B21 = c * nrm(K21)
    B22 = c * nrm(K22)

    return {
        "B11_norm": B11,
        "B12_norm": B12,
        "B21_norm": B21,
        "B22_norm": B22,
        "ratio_B21_over_B11": (B21 / B11) if B11 > 0 else math.inf,
    }

# ═══════════════════════════════════════════════════════════
# §7. Coupures canoniques
# ═══════════════════════════════════════════════════════════

def canonical_tau_cuts(tau_max):
    return {
        "τ^(1/3)": int(np.floor(tau_max ** (1 / 3))),
        "√τ": int(np.floor(np.sqrt(tau_max))),
        "τ^(2/3)": int(np.floor(tau_max ** (2 / 3))),
    }

def canonical_index_cuts(n_tau):
    return {
        "n/4": n_tau // 4,
        "n/2": n_tau // 2,
        "3n/4": (3 * n_tau) // 4,
    }

# ═══════════════════════════════════════════════════════════
# §8. Scan mixte : indice vs seuil arithmétique
# ═══════════════════════════════════════════════════════════

def mixed_scan(tau_list, prime_divisors, a0=1.0, a1=0.25, norm_kind="hs"):
    tau_sorted = sorted(set(int(t) for t in tau_list))
    n_tau = len(tau_sorted)
    tau_max = max(tau_sorted) if tau_sorted else 1

    rows = []

    # Scans par indice (historique)
    _, KQ = build_KQ_global(tau_sorted, prime_divisors, a0, a1)
    for label, k in canonical_index_cuts(n_tau).items():
        small, large, K11, K12, K21, K22 = extract_blocks_by_index(KQ, k)
        vals = lift_block_norms(K11, K12, K21, K22, norm_kind)
        rows.append({
            "mode": "index",
            "label": label,
            "cut_value": k,
            "n_small": len(small),
            "n_large": len(large),
            **vals,
        })

    # Scans par seuil arithmétique
    for label, tau_cut in canonical_tau_cuts(tau_max).items():
        small_tau, large_tau, K11, K12, K21, K22 = build_blocks_by_threshold(
            tau_sorted, tau_cut, prime_divisors, a0, a1
        )
        vals = lift_block_norms(K11, K12, K21, K22, norm_kind)
        rows.append({
            "mode": "threshold",
            "label": label,
            "cut_value": tau_cut,
            "n_small": len(small_tau),
            "n_large": len(large_tau),
            **vals,
        })

    rows.sort(key=lambda r: (r["mode"], r["cut_value"]))
    return rows

# ═══════════════════════════════════════════════════════════
# §9. Main
# ═══════════════════════════════════════════════════════════

def main():
    print("=" * 80)
    print("  SCAN SPATIAL CANONIQUE G2 — v32.31")
    print("  A_q = K_Q ⊗ A_TC,  Ã_q = K_Q ⊗ D")
    print("  Coupure spectrale : M_RS = 0 exactement")
    print("  Coupure spatiale  : B_21 = K_21 ⊗ D (l'objet mesuré)")
    print("  Dédié à Bernard Couret (1928–2010)")
    print("=" * 80)

    for k_primorial in [4, 5, 6]:
        q, primes = primorial(k_primorial)
        tail_primes = [p for p in primes if p > 5]

        if not tail_primes:
            print(f"\n  q = {q} : pas de queues (q ≤ 30), skip")
            continue

        tau_list = build_tau_list(q, primes)
        n_tau = len(tau_list)
        tau_max = max(tau_list) if tau_list else 0

        print(f"\n{'─' * 80}")
        print(f"  q = {q:,}, tail_primes = {tail_primes}, |τ| = {n_tau}, τ_max = {tau_max}")
        print(f"{'─' * 80}")

        if n_tau < 4:
            print("  Trop peu de queues pour un scan significatif, skip")
            continue

        rows = mixed_scan(
            tau_list=tau_list,
            prime_divisors=tail_primes,
            a0=1.0,
            a1=0.25,
            norm_kind="hs",
        )

        # Affichage
        header = (
            f"  {'mode':>10}  {'label':>10}  {'cut':>8}  {'n_sm':>6}  {'n_lg':>6}  "
            f"{'‖B21‖':>12}  {'‖B11‖':>12}  {'B21/B11':>10}"
        )
        print(header)
        print("  " + "─" * (len(header) - 2))

        for r in rows:
            # Filtrer les partitions dégénérées
            if r["n_small"] < 2 or r["n_large"] < 2:
                tag = " (dégénéré)"
            else:
                tag = ""
            print(
                f"  {r['mode']:>10}  {r['label']:>10}  {r['cut_value']:>8}  "
                f"{r['n_small']:>6}  {r['n_large']:>6}  "
                f"{r['B21_norm']:>12.4f}  {r['B11_norm']:>12.4f}  "
                f"{r['ratio_B21_over_B11']:>10.4f}{tag}"
            )

    # Verdict
    print(f"\n{'=' * 80}")
    print("  DIAGNOSTIC")
    print("=" * 80)
    print("""
  La coupure spectrale sur U₃₀ donne M_RS = M_SR = 0 exactement
  (théorème : D est diagonal dans la base des caractères).

  La fuite spatiale B_21 = K_21 ⊗ D mesure le transfert noyau/queue
  dans la variable τ. Le ratio B_21/B_11 est l'objet pertinent pour
  G2 opérateur.

  Convention :
    M_RR, M_RS, M_SR, M_SS = coupure spectrale (M_RS = 0)
    B_11, B_12, B_21, B_22  = coupure spatiale (B_21 ≠ 0)
""")
    print("  RHClaimed = false")
    print("=" * 80)

if __name__ == "__main__":
    main()
