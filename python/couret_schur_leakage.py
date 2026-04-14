#!/usr/bin/env python3
"""
couret_schur_leakage.py — Mesure EFFECTIVE de la fuite hors-diagonale
Programme Couret-Unification v32.28.1 — Condition G2 canonique

Ce script remplace couret_offdiag_proxy.py (v32.28) qui mesurait
le mauvais objet (covariance des moyennes de classes).

Ici on mesure le VRAI observable :
  1. Projeter M(a) sur E₋ = span{χ₃, χ₁₅} (secteur R₃₀) et son
     complément E₊ = E₃ ⊕ E₁ (secteur S₃₀), queue par queue
  2. Calculer le ratio d'énergie S/R (doit → 0 par T9)
  3. Séparer la contribution diagonale (même queue τ) de la
     contribution off-diagonale (queues croisées τ ≠ τ')

Usage : python couret_schur_leakage.py

RHClaimed = false
Dédié à Bernard Couret (1928–2010)
"""

import numpy as np
from math import gcd
from functools import reduce

# ═══════════════════════════════════════════════════════════
# §1. Infrastructure
# ═══════════════════════════════════════════════════════════

def primorial(k):
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    ps = primes[:k]
    q = reduce(lambda a, b: a * b, ps)
    return q, ps

def euler_phi(q, primes):
    phi = q
    for p in primes:
        phi = phi * (p - 1) // p
    return phi

def mobius_sieve(N):
    mu = np.ones(N + 1, dtype=np.int8)
    mu[0] = 0
    is_prime_arr = np.ones(N + 1, dtype=bool)
    is_prime_arr[0] = is_prime_arr[1] = False
    for p in range(2, int(N**0.5) + 1):
        if is_prime_arr[p]:
            for k in range(p * p, N + 1, p * p):
                mu[k] = 0
            for k in range(p, N + 1, p):
                mu[k] = -mu[k]
            for k in range(p * p, N + 1, p):
                is_prime_arr[k] = False
    return mu

def get_coprime_residues(q):
    return [a for a in range(1, q + 1) if gcd(a, q) == 1]

# ═══════════════════════════════════════════════════════════
# §2. Projecteurs spectraux sur U₃₀ (issus de T3)
# ═══════════════════════════════════════════════════════════

U30 = [1, 7, 11, 13, 17, 19, 23, 29]
U30_IDX = {r: i for i, r in enumerate(U30)}

def build_characters_mod30():
    """
    Les 8 caractères de (Z/30Z)* dans l'ordre canonique.
    Construits via CRT : (Z/30Z)* ≅ (Z/2Z) × (Z/3Z)* × (Z/5Z)*
    avec générateurs 11 (ordre 2) et 7 (ordre 4).
    """
    chars = np.zeros((8, 8), dtype=complex)
    # chi_{a,b} : chi(7) = i^a, chi(11) = (-1)^b
    # Résoudre : chaque r ∈ U₃₀ = 7^α · 11^β mod 30
    
    # Table de décomposition r → (α, β)
    decomp = {}
    for alpha in range(4):
        for beta in range(2):
            r = (pow(7, alpha, 30) * pow(11, beta, 30)) % 30
            decomp[r] = (alpha, beta)
    
    idx = 0
    for a in range(4):
        for b in range(2):
            for j, r in enumerate(U30):
                alpha, beta = decomp[r]
                chars[idx, j] = (1j ** a) ** alpha * ((-1) ** b) ** beta
            idx += 1
    
    return chars

def build_projectors():
    """
    Construit les projecteurs spectraux P₃, P₁, P₋ sur U₃₀.
    
    Spectre de A_TC : {3², 1⁴, (-1)²}
    
    Les valeurs propres de chaque caractère :
      χ(1) + χ(11) + χ(29) pour TC = {1, 11, 29}
    """
    chars = build_characters_mod30()
    
    # Calculer la valeur propre de chaque caractère
    # λ_χ = χ(1) + χ(11) + χ(29)
    eigenvalues = np.zeros(8, dtype=complex)
    for i in range(8):
        idx_1 = U30_IDX[1]
        idx_11 = U30_IDX[11]
        idx_29 = U30_IDX[29]
        eigenvalues[i] = chars[i, idx_1] + chars[i, idx_11] + chars[i, idx_29]
    
    # Classifier : λ ≈ 3, 1, ou -1
    E3_indices = []
    E1_indices = []
    Em1_indices = []
    
    for i in range(8):
        lam = eigenvalues[i].real
        if abs(lam - 3) < 0.01:
            E3_indices.append(i)
        elif abs(lam - 1) < 0.01:
            E1_indices.append(i)
        elif abs(lam + 1) < 0.01:
            Em1_indices.append(i)
    
    assert len(E3_indices) == 2, f"E3: {E3_indices}"
    assert len(E1_indices) == 4, f"E1: {E1_indices}"
    assert len(Em1_indices) == 2, f"E-1: {Em1_indices}"
    
    # Projecteur P₋ (sur E₋₁ = secteur de défaut R₃₀)
    # P₋(f) = (1/8) Σ_{χ ∈ E₋₁} ⟨f, χ⟩ χ
    # En matriciel : P₋ = (1/8) Σ_{i ∈ Em1} χ_i^H ⊗ χ_i
    P_minus = np.zeros((8, 8), dtype=complex)
    for i in Em1_indices:
        chi = chars[i]
        P_minus += np.outer(chi, chi.conj()) / 8.0
    
    # Projecteur P₊ = I - P₋ (secteur S₃₀)
    P_plus = np.eye(8, dtype=complex) - P_minus
    
    return P_minus, P_plus, E3_indices, E1_indices, Em1_indices, chars, eigenvalues

# ═══════════════════════════════════════════════════════════
# §3. Décomposition par queues CRT
# ═══════════════════════════════════════════════════════════

def decompose_by_tails(q, primes, M_vec, residues):
    """
    Décompose G_q par CRT : a ↦ (a mod 30, tail).
    Retourne un dict {tail → array de 8 valeurs M(a) par classe mod 30}.
    """
    # La "queue" τ est le tuple (a mod p) pour p | q, p > 5
    tail_primes = [p for p in primes if p > 5]
    
    tails = {}
    for i, a in enumerate(residues):
        r30 = a % 30
        tau = tuple(a % p for p in tail_primes) if tail_primes else (0,)
        
        if tau not in tails:
            tails[tau] = np.zeros(8, dtype=float)
        
        idx30 = U30_IDX[r30]
        tails[tau][idx30] = M_vec[i]
    
    return tails

# ═══════════════════════════════════════════════════════════
# §4. Mesure effective de la fuite de Schur
# ═══════════════════════════════════════════════════════════

def measure_schur_leakage(q, primes, N_max=2_000_000):
    """
    Mesure la fuite de Schur effective.
    
    Pour chaque queue τ, on projette le 8-vecteur M_τ sur E₋ et E₊.
    On calcule :
      - énergie R : Σ_τ ‖P₋(M_τ)‖²
      - énergie S : Σ_τ ‖P₊(M_τ)‖²
      - ratio S/R (doit → 0 par T9)
      - M₂₁^diag : Σ_τ ‖P₊(M_τ)‖ · ‖P₋(M_τ)‖  (même queue)
      - M₂₁^off_HS² : Σ_{τ≠τ'} |⟨P₊(M_τ), P₋(M_τ')⟩|²  (queues croisées)
    """
    phi_q = euler_phi(q, primes)
    
    print(f"\n  q = {q}, φ(q) = {phi_q}")
    
    # Crible
    mu = mobius_sieve(N_max)
    M_full = np.cumsum(mu[:N_max + 1])
    
    # Résidus copremiers
    residues = get_coprime_residues(q)
    assert len(residues) == phi_q
    
    # Vecteur de Mertens
    M_vec = np.array([M_full[a] for a in residues], dtype=float)
    c0 = np.mean(M_vec ** 2)
    
    # Projecteurs
    P_minus, P_plus, E3_idx, E1_idx, Em1_idx, chars, evals = build_projectors()
    
    # Vérifier les projecteurs
    print(f"  Eigenvalues : {[f'{e.real:.0f}' for e in evals]}")
    print(f"  E₋₁ indices : {Em1_idx} (secteur R₃₀ = défaut)")
    print(f"  E₃ indices  : {E3_idx}")
    print(f"  E₁ indices  : {E1_idx}")
    
    # Décomposer par queues
    tails = decompose_by_tails(q, primes, M_vec, residues)
    n_tails = len(tails)
    
    print(f"  Nombre de queues τ : {n_tails} (attendu : φ(q)/8 = {phi_q // 8})")
    
    # Pour chaque queue, projeter sur R₃₀ et S₃₀
    R_projections = {}  # τ → P₋(M_τ)
    S_projections = {}  # τ → P₊(M_τ)
    
    energy_R_total = 0.0
    energy_S_total = 0.0
    
    for tau, m_tau in tails.items():
        r_proj = P_minus @ m_tau  # projection sur E₋₁
        s_proj = P_plus @ m_tau   # projection sur E₊
        
        R_projections[tau] = r_proj.real
        S_projections[tau] = s_proj.real
        
        energy_R_total += np.sum(np.abs(r_proj) ** 2)
        energy_S_total += np.sum(np.abs(s_proj) ** 2)
    
    # Normaliser
    energy_R_norm = energy_R_total / phi_q
    energy_S_norm = energy_S_total / phi_q
    ratio_SR = energy_S_norm / energy_R_norm if energy_R_norm > 0 else float('inf')
    
    # Vérification Pythagore
    energy_total = energy_R_norm + energy_S_norm
    pythagore_err = abs(c0 - energy_total) / c0 if c0 > 0 else 0
    
    # ─── M₂₁ : couplage entre R et S ───
    
    # M₂₁^diag : énergie de couplage INTRA queue
    # Pour chaque τ : ⟨P₊(M_τ), P₋(M_τ)⟩
    diag_coupling = 0.0
    for tau in tails:
        cross = np.dot(S_projections[tau], R_projections[tau])
        diag_coupling += cross ** 2
    
    # M₂₁^off : énergie de couplage INTER queues
    # Pour τ ≠ τ' : ⟨P₊(M_τ), P₋(M_τ')⟩
    off_coupling = 0.0
    tau_list = list(tails.keys())
    
    # Méthode efficace : utiliser les vecteurs empilés
    # R_matrix[i] = R_projections[tau_i], S_matrix[i] = S_projections[tau_i]
    R_matrix = np.array([R_projections[tau] for tau in tau_list])
    S_matrix = np.array([S_projections[tau] for tau in tau_list])
    
    # Matrice de couplage croisé : C[i,j] = ⟨S_i, R_j⟩
    coupling_matrix = S_matrix @ R_matrix.T
    
    # Énergie totale du couplage
    total_coupling_HS = np.sum(coupling_matrix ** 2)
    
    # Énergie diagonale
    diag_coupling_HS = np.sum(np.diag(coupling_matrix) ** 2)
    
    # Énergie off-diagonale
    off_coupling_HS = total_coupling_HS - diag_coupling_HS
    
    # Ratio off/diag
    if diag_coupling_HS > 0:
        off_diag_ratio = off_coupling_HS / diag_coupling_HS
    else:
        off_diag_ratio = 0.0
    
    # Ratio off/total
    if total_coupling_HS > 0:
        off_total_ratio = off_coupling_HS / total_coupling_HS
    else:
        off_total_ratio = 0.0
    
    return {
        'q': q,
        'phi_q': phi_q,
        'n_tails': n_tails,
        'c0': c0,
        'energy_R': energy_R_norm,
        'energy_S': energy_S_norm,
        'ratio_SR': ratio_SR,
        'pythagore_err': pythagore_err,
        'diag_coupling_HS': diag_coupling_HS,
        'off_coupling_HS': off_coupling_HS,
        'total_coupling_HS': total_coupling_HS,
        'off_diag_ratio': off_diag_ratio,
        'off_total_ratio': off_total_ratio,
    }

# ═══════════════════════════════════════════════════════════
# §5. Main
# ═══════════════════════════════════════════════════════════

def main():
    print("=" * 76)
    print("  MESURE EFFECTIVE DE LA FUITE DE SCHUR — v32.28.1")
    print("  Condition G2 canonique pour gel de L10")
    print("  Observable : ‖M₂₁^off‖_HS via projecteurs E₋/E₊")
    print("  Dédié à Bernard Couret (1928–2010)")
    print("=" * 76)
    
    N_max = 2_000_000
    results = []
    
    for k in [3, 4, 5]:  # q = 30, 210, 2310
        q, primes = primorial(k)
        r = measure_schur_leakage(q, primes, N_max)
        results.append(r)
    
    # ─── Tableau 1 : Énergie R vs S (T9) ───
    print("\n" + "─" * 76)
    print("  TABLEAU 1 — LOCALISATION DE SCHUR (T9)")
    print("  E_R = énergie dans R₃₀ (défaut), E_S = énergie dans S₃₀")
    print("─" * 76)
    print(f"  {'q':>6}  {'φ(q)':>6}  {'τ':>5}  {'E_R':>10}  {'E_S':>10}  "
          f"{'S/R':>8}  {'Pyth':>6}")
    print("  " + "─" * 60)
    
    for r in results:
        pyth = "✅" if r['pythagore_err'] < 0.001 else f"❌{r['pythagore_err']:.1e}"
        print(f"  {r['q']:>6}  {r['phi_q']:>6}  {r['n_tails']:>5}  "
              f"{r['energy_R']:>10.2f}  {r['energy_S']:>10.2f}  "
              f"{r['ratio_SR']:>8.4f}  {pyth:>6}")
    
    # ─── Tableau 2 : M₂₁ diag vs off (G2) ───
    print("\n" + "─" * 76)
    print("  TABLEAU 2 — FUITE HORS-DIAGONALE M₂₁^off (G2)")
    print("  diag = couplage intra-queue, off = couplage inter-queues")
    print("─" * 76)
    print(f"  {'q':>6}  {'‖diag‖²_HS':>14}  {'‖off‖²_HS':>14}  "
          f"{'off/diag':>10}  {'off/total':>10}")
    print("  " + "─" * 60)
    
    for r in results:
        print(f"  {r['q']:>6}  {r['diag_coupling_HS']:>14.4f}  "
              f"{r['off_coupling_HS']:>14.4f}  "
              f"{r['off_diag_ratio']:>10.4%}  "
              f"{r['off_total_ratio']:>10.4%}")
    
    # ─── Verdict ───
    print("\n" + "=" * 76)
    print("  VERDICT")
    print("=" * 76)
    
    # T9 : ratio S/R doit décroître
    print("\n  T9 (localisation de Schur) :")
    for r in results:
        status = "✅" if r['ratio_SR'] < 1 else "⚠"
        print(f"    q={r['q']:>6} : S/R = {r['ratio_SR']:.4f}  {status}")
    
    if len(results) >= 2:
        trend_SR = results[-1]['ratio_SR'] - results[0]['ratio_SR']
        print(f"    Tendance S/R : {'DÉCROISSANTE ↓ ✅' if trend_SR < 0 else 'CROISSANTE ↑ ⚠'}")
    
    # G2 : off/diag ou off/total doit être petit
    print("\n  G2 (fuite hors-diagonale) :")
    last = results[-1]
    
    if last['off_diag_ratio'] < 0.02:
        print(f"    off/diag à q={last['q']} : {last['off_diag_ratio']:.4%} < 2%")
        print("    ✅ Condition G2 SATISFAITE")
    elif last['off_diag_ratio'] < 0.10:
        print(f"    off/diag à q={last['q']} : {last['off_diag_ratio']:.4%} < 10%")
        print("    ⚠  Condition G2 marginale — à confirmer")
    else:
        print(f"    off/diag à q={last['q']} : {last['off_diag_ratio']:.4%}")
        print("    ❌ Condition G2 non satisfaite")
    
    if len(results) >= 2:
        trend_off = results[-1]['off_diag_ratio'] - results[-2]['off_diag_ratio']
        print(f"    Tendance off/diag : {'DÉCROISSANTE ↓' if trend_off < 0 else 'CROISSANTE ↑'}")
    
    print(f"\n  RHClaimed = false")
    print("=" * 76)

if __name__ == "__main__":
    main()
