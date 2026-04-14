#!/usr/bin/env python3
"""
couret_rs1_enriched_tests.py — Reproduction des tests RS1 enrichis
Programme Couret-Unification — Condition G1 pour gel de L10

Objectif : reproduire le tableau 10_RS1_enriched_tests.md
    - Projection sur V_{q,P} (produit tensoriel, caractères locaux complets)
    - Vérifier ratio C₁/c₀ ≈ 66% stable
    - Centrage exact du résidu
    - Marge δ = (√C₁ - √C₂')² > 0

Usage : python couret_rs1_enriched_tests.py

RHClaimed = false
Dédié à Bernard Couret (1928–2010)
"""

import numpy as np
from math import gcd
from functools import reduce
from itertools import product as iterproduct

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

def get_coprime_residues(q, primes):
    return np.array([a for a in range(1, q + 1) if gcd(a, q) == 1])

def build_basis_mod30():
    """
    Base minimale F₃₀ᵐⁱⁿ sur U₃₀ = {1,7,11,13,17,19,23,29}.
    5 fonctions (F₀ exclus car redondant avec centrage).
    """
    U30 = [1, 7, 11, 13, 17, 19, 23, 29]
    TC = {1, 11, 29}
    
    basis = {}
    
    # F_C : bloc Couret centré
    basis['F_C'] = np.array([1.0 if r in TC else 0.0 for r in U30]) - 3.0/8.0
    
    # F_19 : canal fantôme centré
    basis['F_19'] = np.array([1.0 if r == 19 else 0.0 for r in U30]) - 1.0/8.0
    
    # chi_3 : caractère quadratique mod 3
    basis['chi_3'] = np.array([1.0 if r % 3 == 1 else -1.0 for r in U30])
    
    # chi_5 : caractère quadratique mod 5
    def leg5(r):
        return 1.0 if (r % 5) in [1, 4] else -1.0
    basis['chi_5'] = np.array([leg5(r) for r in U30])
    
    # chi_15 : produit
    basis['chi_15'] = basis['chi_3'] * basis['chi_5']
    
    return U30, basis

def build_local_characters(p):
    """
    Base complète des caractères de (Z/pZ)*.
    Retourne une matrice (p-1) × (p-1) où chaque ligne est un caractère.
    """
    # Trouver un générateur primitif
    for g in range(2, p):
        seen = set()
        val = 1
        for _ in range(p - 1):
            seen.add(val)
            val = (val * g) % p
        if len(seen) == p - 1:
            break
    
    # Construire les p-1 caractères
    residues_p = [(g ** k) % p for k in range(p - 1)]  # ordonnés par puissance
    chars = np.zeros((p - 1, p - 1), dtype=complex)
    
    omega = np.exp(2j * np.pi / (p - 1))
    for j in range(p - 1):  # j-ème caractère
        for k in range(p - 1):  # k-ème résidu (= g^k)
            chars[j, k] = omega ** (j * k)
    
    return residues_p, chars

def project_enriched(q, primes, P_horizon, N_max=2_000_000):
    """
    Projette M(a) sur V_{q,P} = F₃₀ᵐⁱⁿ ⊗ ∏_{5<p≤P} H_p.
    
    Retourne C₁, ‖R‖², c₀, et les diagnostics.
    """
    phi_q = euler_phi(q, primes)
    
    # Primes locaux à enrichir
    local_primes = [p for p in primes if 5 < p <= P_horizon]
    
    # Dimensions
    U30, basis30 = build_basis_mod30()
    dim_30 = len(basis30)  # 5
    dim_local = 1
    for p in local_primes:
        dim_local *= (p - 1)
    dim_total = dim_30 * dim_local
    
    print(f"\n  q={q}, P={P_horizon}, φ(q)={phi_q}, dim(V)={dim_total}")
    
    # Crible
    mu = mobius_sieve(N_max)
    M_full = np.cumsum(mu[:N_max + 1])
    
    # Résidus copremiers
    residues = get_coprime_residues(q, primes)
    assert len(residues) == phi_q
    
    # Vecteur de Mertens
    M_vec = np.array([M_full[a] for a in residues], dtype=np.float64)
    
    # c₀(q) = ‖M‖²
    c0 = np.mean(M_vec ** 2)
    
    # Construire la matrice de projection
    # Chaque colonne = une fonction de base relevée à G_q
    
    # Préparer les caractères locaux
    local_chars = {}
    local_residues = {}
    for p in local_primes:
        res_p, chars_p = build_local_characters(p)
        local_chars[p] = chars_p
        local_residues[p] = res_p
    
    # Construire la base tensorielle
    # Pour chaque combinaison (f30, chi_p1, chi_p2, ...)
    n_basis = dim_total
    Phi = np.zeros((phi_q, n_basis), dtype=complex)
    
    basis_names = list(basis30.keys())
    
    if len(local_primes) == 0:
        # Pas de facteurs locaux
        local_indices = [range(1)]
        local_dims = [1]
    else:
        local_indices = [range(p - 1) for p in local_primes]
        local_dims = [p - 1 for p in local_primes]
    
    col = 0
    for b_idx, bname in enumerate(basis_names):
        f30 = basis30[bname]
        
        for local_combo in iterproduct(*local_indices):
            # Construire la fonction tensorielle
            for i, a in enumerate(residues):
                # Composante mod 30
                r30 = a % 30
                idx30 = U30.index(r30)
                val = f30[idx30]
                
                # Composantes locales
                for lp_idx, p in enumerate(local_primes):
                    r_p = a % p
                    # Trouver l'index de r_p dans local_residues[p]
                    try:
                        k = local_residues[p].index(r_p)
                    except ValueError:
                        val = 0  # r_p = 0, pas copremier
                        break
                    chi_idx = local_combo[lp_idx]
                    val *= local_chars[p][chi_idx, k]
                
                Phi[i, col] = val
            col += 1
    
    assert col == n_basis, f"col={col}, n_basis={n_basis}"
    
    # Projection orthogonale de M sur V
    # M_main = Phi (Phi^H Phi)^{-1} Phi^H M
    
    # Matrice de Gram (devrait être indépendante de q par CRT)
    Gram = (Phi.conj().T @ Phi) / phi_q
    
    # Vecteur b = Phi^H M / φ(q)
    b = (Phi.conj().T @ M_vec) / phi_q
    
    # Coefficients c = Gram^{-1} b
    try:
        c = np.linalg.solve(Gram, b)
    except np.linalg.LinAlgError:
        print("  ⚠ Matrice de Gram singulière — base redondante")
        # Utiliser pseudo-inverse
        c = np.linalg.lstsq(Gram, b, rcond=None)[0]
    
    # M_main = Phi c
    M_main = (Phi @ c).real
    
    # Résidu
    R = M_vec - M_main
    
    # Masses
    C1 = np.mean(M_main ** 2)
    R_norm = np.mean(R ** 2)
    
    # Centrage du résidu
    R_sum = np.sum(R)
    
    # Vérification Pythagore
    pythagore_check = abs(c0 - C1 - R_norm)
    
    # Marge δ = (√C₁ - √C₂')²
    if C1 > R_norm:
        margin = (np.sqrt(C1) - np.sqrt(R_norm)) ** 2
    else:
        margin = 0.0
    
    ratio = C1 / c0 if c0 > 0 else 0
    
    return {
        'q': q,
        'P': P_horizon,
        'phi_q': phi_q,
        'dim_V': dim_total,
        'c0': c0,
        'C1': C1,
        'R_norm': R_norm,
        'ratio': ratio,
        'margin': margin,
        'R_sum': R_sum,
        'pythagore_err': pythagore_check,
    }

def main():
    print("=" * 76)
    print("  RS1 ENRICHED TESTS — Condition G1 pour gel de L10")
    print("  Reproduction du tableau 10_RS1_enriched_tests.md")
    print("  Dédié à Bernard Couret (1928–2010)")
    print("=" * 76)
    
    N_max = 2_000_000
    
    # Tests à exécuter
    tests = [
        # (k_primorial, P_horizon)
        (5, 5),    # q=2310, base mod 30 seule (dim 5)
        (5, 7),    # q=2310, enrichi P=7 (dim 30)
        (5, 11),   # q=2310, enrichi P=11 (dim 300)
        (6, 13),   # q=30030, enrichi P=13 (dim 3600)
    ]
    
    results = []
    for k, P in tests:
        q, primes = primorial(k)
        r = project_enriched(q, primes, P, N_max)
        results.append(r)
    
    # Tableau récapitulatif
    print("\n" + "─" * 76)
    print("  TABLEAU RS1 ENRICHI — CONDITION G1")
    print("─" * 76)
    print(f"  {'q':>6}  {'P':>3}  {'φ(q)':>6}  {'dim':>5}  {'c₀':>10}  "
          f"{'C₁':>10}  {'C₁/c₀':>7}  {'δ':>8}  {'ΣR':>10}")
    print("  " + "─" * 70)
    
    for r in results:
        print(f"  {r['q']:>6}  {r['P']:>3}  {r['phi_q']:>6}  {r['dim_V']:>5}  "
              f"{r['c0']:>10.3f}  {r['C1']:>10.3f}  {r['ratio']:>7.1%}  "
              f"{r['margin']:>8.3f}  {r['R_sum']:>10.4f}")
    
    # Vérifications
    print("\n" + "─" * 76)
    print("  VÉRIFICATIONS DE COHÉRENCE")
    print("─" * 76)
    
    for r in results:
        checks = []
        # Test A : Pythagore
        if r['pythagore_err'] < 1e-6:
            checks.append("Pythagore ✅")
        else:
            checks.append(f"Pythagore ❌ (err={r['pythagore_err']:.2e})")
        
        # Test B : Centrage
        if abs(r['R_sum']) < 1e-6:
            checks.append("Centrage ✅")
        else:
            checks.append(f"Centrage ⚠ (ΣR={r['R_sum']:.4f})")
        
        # Test C : Positivité de C₁
        if r['C1'] > 0:
            checks.append("C₁>0 ✅")
        else:
            checks.append("C₁>0 ❌")
        
        # Test D : Marge positive
        if r['margin'] > 0:
            checks.append(f"δ>0 ✅")
        else:
            checks.append("δ>0 ❌")
        
        print(f"  q={r['q']}, P={r['P']} : {' | '.join(checks)}")
    
    # Verdict
    print("\n" + "=" * 76)
    print("  VERDICT — CONDITION G1")
    print("=" * 76)
    
    # Vérifier stabilité du ratio
    enriched = [r for r in results if r['dim_V'] >= 300]
    if len(enriched) >= 2:
        ratios = [r['ratio'] for r in enriched]
        ratio_std = np.std(ratios)
        ratio_mean = np.mean(ratios)
        
        print(f"\n  Ratio C₁/c₀ moyen (dim≥300) : {ratio_mean:.1%}")
        print(f"  Écart-type : {ratio_std:.1%}")
        
        if ratio_std < 0.02 and all(r['margin'] > 0 for r in enriched):
            print("  ✅ Ratio stable (~66%), marge positive")
            print("  ✅ Condition G1 SATISFAITE")
            print("  RS1 passe de [C/I] à [C/N]")
        else:
            print("  ⚠ Ratio instable ou marge négative")
            print("  Condition G1 à confirmer")
    
    print(f"\n  RHClaimed = false")
    print("=" * 76)

if __name__ == "__main__":
    main()
