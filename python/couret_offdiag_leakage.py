#!/usr/bin/env python3
"""
couret_offdiag_leakage.py — Mesure de la fuite hors-diagonale M₂₁^off
Programme Couret-Unification — Condition G2 pour gel de L10

Objectif : mesurer ‖M₂₁^off‖_HS à q=2310 et q=30030
Si la fuite reste < 2% de la masse diagonale, T9 est numériquement verrouillé.

Usage : python couret_offdiag_leakage.py

RHClaimed = false
Dédié à Bernard Couret (1928–2010)
"""

import numpy as np
from math import gcd
from functools import reduce

def primorial(k):
    """Retourne le k-ième primoriel et la liste des premiers."""
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    ps = primes[:k]
    q = reduce(lambda a, b: a * b, ps)
    return q, ps

def euler_phi(q, primes):
    """φ(q) pour q primoriel."""
    phi = q
    for p in primes:
        phi = phi * (p - 1) // p
    return phi

def mobius_sieve(N):
    """Crible de Möbius jusqu'à N."""
    mu = np.ones(N + 1, dtype=np.int8)
    mu[0] = 0
    is_prime = np.ones(N + 1, dtype=bool)
    is_prime[0] = is_prime[1] = False
    for p in range(2, int(N**0.5) + 1):
        if is_prime[p]:
            # Marquer les multiples de p²
            for k in range(p * p, N + 1, p * p):
                mu[k] = 0
            # Flip le signe pour les multiples simples de p
            for k in range(p, N + 1, p):
                mu[k] = -mu[k]
            # Crible d'Ératosthène
            for k in range(p * p, N + 1, p):
                is_prime[k] = False
    return mu

def mertens_values(mu, N):
    """M(n) = Σ_{k≤n} μ(k) pour n = 1..N."""
    M = np.cumsum(mu[:N + 1])
    return M

def get_coprime_residues(q, primes):
    """Liste des a ∈ {1,...,q} avec (a,q)=1."""
    residues = []
    for a in range(1, q + 1):
        if gcd(a, q) == 1:
            residues.append(a)
    return np.array(residues)

def dirichlet_characters_mod30():
    """
    Retourne les 8 caractères de (Z/30Z)* évalués sur les 8 résidus.
    Résidus : [1, 7, 11, 13, 17, 19, 23, 29]
    """
    residues = [1, 7, 11, 13, 17, 19, 23, 29]
    # Table des caractères mod 30 (via CRT : Z/30 ≅ Z/2 × Z/3 × Z/5)
    # chi_0 = trivial
    chi = np.zeros((8, 8), dtype=complex)
    
    # Caractère trivial
    chi[0] = np.ones(8)
    
    # Construire via les générateurs
    # ord(7) = 4 dans (Z/30Z)*, ord(11) = 2
    # chi_{a,b}(7) = i^a, chi_{a,b}(11) = (-1)^b
    gen7_powers = {}  # r -> puissance de 7 qui donne r
    g = 1
    for k in range(4):
        gen7_powers[g % 30] = k
        g = (g * 7) % 30
    
    gen11_powers = {}
    g = 1
    for k in range(2):
        gen11_powers[g % 30] = k
        g = (g * 11) % 30
    
    idx = 0
    for a in range(4):
        for b in range(2):
            for j, r in enumerate(residues):
                # Trouver r = 7^α · 11^β mod 30
                # Utiliser la table de multiplication
                val = 1.0 + 0j
                found = False
                for alpha in range(4):
                    for beta in range(2):
                        if (pow(7, alpha, 30) * pow(11, beta, 30)) % 30 == r:
                            val = (1j ** a) ** alpha * ((-1) ** b) ** beta
                            found = True
                            break
                    if found:
                        break
                chi[idx, j] = val
            idx += 1
    
    return residues, chi

def compute_offdiag_leakage(q, primes, N_max=2_000_000):
    """
    Calcule la fuite hors-diagonale pour le primoriel q.
    
    Retourne :
    - masse_diag : ‖M₂₁^diag‖² (blocs alignés par queue)
    - masse_off  : ‖M₂₁^off‖²  (couplage entre queues distinctes)
    - ratio      : masse_off / masse_diag
    """
    phi_q = euler_phi(q, primes)
    
    print(f"\n  Calcul pour q = {q}, φ(q) = {phi_q}")
    print(f"  Crible de Möbius jusqu'à N = {N_max:,}...")
    
    mu = mobius_sieve(N_max)
    M = mertens_values(mu, N_max)
    
    # Résidus copremiers
    residues = get_coprime_residues(q, primes)
    assert len(residues) == phi_q
    
    # Vecteur de Mertens sur les copremiers
    # M(a) pour a ∈ {1,...,q}, (a,q)=1
    M_vec = np.array([M[a] for a in residues], dtype=np.float64)
    
    # Moyenne
    M_mean = np.mean(M_vec)
    
    # Masse totale c₀(q)
    c0 = np.mean(M_vec ** 2)
    
    # Classification par résidu mod 30
    res_mod30 = residues % 30
    classes_30 = {}
    for i, r30 in enumerate(res_mod30):
        if r30 not in classes_30:
            classes_30[r30] = []
        classes_30[r30].append(i)
    
    # Partie diagonale : variance INTRA chaque classe mod 30
    # (blocs alignés par la même queue mod 30)
    masse_diag = 0.0
    for r30, indices in classes_30.items():
        vals = M_vec[indices]
        mean_class = np.mean(vals)
        # La contribution diagonale est la variance au sein de chaque classe
        # plus la contribution de la moyenne de classe
        masse_diag += np.sum(vals ** 2)
    masse_diag /= phi_q
    
    # Partie hors-diagonale : covariance INTER classes mod 30
    # M₂₁^off mesure le couplage entre classes distinctes
    # Par Pythagore : masse_totale = masse_intra + masse_inter
    # masse_inter = Σ_{r≠s} Σ_{i∈class_r, j∈class_s} M(a_i)·M(a_j) / φ(q)²
    
    # Plus précisément, pour les blocs de Schur :
    # masse_diag = somme des ‖blocs diagonaux‖²
    # masse_off = somme des ‖blocs hors-diagonaux‖²
    
    # Calcul via les moyennes par classe
    class_means = {}
    class_vars = {}
    for r30, indices in classes_30.items():
        vals = M_vec[indices]
        class_means[r30] = np.mean(vals)
        class_vars[r30] = np.var(vals)
    
    # Matrice de covariance inter-classes (8×8 pour mod 30)
    residues_30 = sorted(classes_30.keys())
    n_classes = len(residues_30)
    cov_matrix = np.zeros((n_classes, n_classes))
    
    for i, r1 in enumerate(residues_30):
        for j, r2 in enumerate(residues_30):
            vals1 = M_vec[classes_30[r1]]
            vals2 = M_vec[classes_30[r2]]
            # Covariance croisée normalisée
            cov_matrix[i, j] = np.mean(vals1) * np.mean(vals2)
    
    # La fuite hors-diagonale est la norme HS de la partie off-diag
    # de la matrice de covariance inter-classes
    diag_energy = np.sum(np.diag(cov_matrix) ** 2)
    total_energy = np.sum(cov_matrix ** 2)
    offdiag_energy = total_energy - diag_energy
    
    # Ratio de fuite
    if diag_energy > 0:
        ratio = offdiag_energy / diag_energy
    else:
        ratio = float('inf')
    
    # Aussi : mesure directe par DFT
    # La fuite se mesure mieux par les caractères non-principaux mod 30
    _, chi_table = dirichlet_characters_mod30()
    res30_list = [1, 7, 11, 13, 17, 19, 23, 29]
    
    # Moyennes de M par classe mod 30
    m_by_class = np.zeros(8)
    for i, r30 in enumerate(res30_list):
        if r30 in classes_30:
            m_by_class[i] = np.mean(M_vec[classes_30[r30]])
    
    # Transformée de Fourier sur (Z/30Z)*
    fourier_coeffs = chi_table @ m_by_class
    
    # Énergie spectrale par caractère
    spectral_energy = np.abs(fourier_coeffs) ** 2
    
    # Partie diagonale (chi_0) vs non-principale
    energy_principal = spectral_energy[0]
    energy_nonprincipal = np.sum(spectral_energy[1:])
    
    return {
        'q': q,
        'phi_q': phi_q,
        'c0': c0,
        'masse_diag': diag_energy,
        'masse_off': offdiag_energy,
        'ratio_leakage': ratio,
        'energy_principal': energy_principal,
        'energy_nonprincipal': energy_nonprincipal,
        'spectral_energy': spectral_energy,
        'class_means': class_means,
    }

def main():
    print("=" * 76)
    print("  MESURE DE LA FUITE HORS-DIAGONALE M₂₁^off")
    print("  Condition G2 pour gel de L10")
    print("  Dédié à Bernard Couret (1928–2010)")
    print("=" * 76)
    
    N_max = 2_000_000
    
    results = []
    
    for k in [3, 4, 5]:  # q = 30, 210, 2310
        q, primes = primorial(k)
        r = compute_offdiag_leakage(q, primes, N_max)
        results.append(r)
    
    # Tableau récapitulatif
    print("\n" + "─" * 76)
    print("  TABLEAU RÉCAPITULATIF — FUITE HORS-DIAGONALE")
    print("─" * 76)
    print(f"  {'q':>8}  {'φ(q)':>6}  {'c₀(q)':>12}  {'E_diag':>12}  {'E_off':>12}  {'Ratio':>8}")
    print(f"  {'':>8}  {'':>6}  {'':>12}  {'':>12}  {'':>12}  {'off/diag':>8}")
    print("  " + "─" * 68)
    
    for r in results:
        print(f"  {r['q']:>8}  {r['phi_q']:>6}  {r['c0']:>12.4f}  "
              f"{r['masse_diag']:>12.4f}  {r['masse_off']:>12.6f}  "
              f"{r['ratio_leakage']:>8.4%}")
    
    # Diagnostic spectral
    print("\n" + "─" * 76)
    print("  DIAGNOSTIC SPECTRAL MOD 30")
    print("─" * 76)
    
    for r in results:
        total = r['energy_principal'] + r['energy_nonprincipal']
        ratio_np = r['energy_nonprincipal'] / total if total > 0 else 0
        print(f"  q = {r['q']:>6} : E_princ = {r['energy_principal']:>10.2f}, "
              f"E_non_princ = {r['energy_nonprincipal']:>10.2f}, "
              f"ratio = {ratio_np:.4%}")
    
    # Moyennes par classe
    print("\n" + "─" * 76)
    print("  MOYENNES DE M(a) PAR CLASSE MOD 30")
    print("─" * 76)
    
    for r in results:
        means = r['class_means']
        print(f"\n  q = {r['q']}, φ(q) = {r['phi_q']}:")
        for r30 in sorted(means.keys()):
            print(f"    classe {r30:>2} : <M> = {means[r30]:>10.4f}")
    
    # Verdict
    print("\n" + "=" * 76)
    print("  VERDICT — CONDITION G2")
    print("=" * 76)
    
    last = results[-1]
    if last['ratio_leakage'] < 0.02:
        print(f"\n  Fuite à q={last['q']} : {last['ratio_leakage']:.4%} < 2%")
        print("  ✅ Condition G2 SATISFAITE")
        print("  T9 numériquement verrouillé")
    elif last['ratio_leakage'] < 0.05:
        print(f"\n  Fuite à q={last['q']} : {last['ratio_leakage']:.4%} < 5%")
        print("  ⚠  Condition G2 marginale — à confirmer à q=30030")
    else:
        print(f"\n  Fuite à q={last['q']} : {last['ratio_leakage']:.4%} ≥ 5%")
        print("  ❌ Condition G2 NON satisfaite — investigation requise")
    
    # Tendance
    if len(results) >= 2:
        trend = results[-1]['ratio_leakage'] - results[-2]['ratio_leakage']
        direction = "DÉCROISSANTE ↓" if trend < 0 else "CROISSANTE ↑"
        print(f"  Tendance de la fuite : {direction}")
    
    print(f"\n  RHClaimed = false")
    print("=" * 76)

if __name__ == "__main__":
    main()
