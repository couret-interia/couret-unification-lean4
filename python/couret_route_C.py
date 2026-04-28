#!/usr/bin/env python3
"""
couret_route_C.py — Attaque directe du verrou κ par Route C
Programme Couret-Unification v32.29 — Front principal actif

Route C : décomposer κ(q)² via inclusion-exclusion
  κ(q)² = (1/φ(q)) Σ_{d|q} μ(d) S_d(q)
  où S_d(q) = Σ_{d|n, n≤q} M(n)²

Si S_1(q) ~ q²/(2π²) domine les termes d'erreur,
alors κ(q)² ~ q/(2π² · φ(q)/q) → ∞.

Ce script :
  1. Calcule S_d(q) pour tout d | q
  2. Vérifie la domination de S_1
  3. Compare κ(q)² observé vs prédiction Route C
  4. Pousse jusqu'à q₈ = 9699690 si mémoire le permet

Usage : python couret_route_C.py

RHClaimed = false
Dédié à Bernard Couret (1928–1999)
"""

import numpy as np
from math import gcd, log, pi, exp
from functools import reduce
from collections import defaultdict

# ═══════════════════════════════════════════════════════════
# §1. Infrastructure
# ═══════════════════════════════════════════════════════════

EULER_GAMMA = 0.5772156649015329

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
    """Crible de Möbius jusqu'à N."""
    mu = np.zeros(N + 1, dtype=np.int8)
    mu[1] = 1
    is_prime = np.ones(N + 1, dtype=bool)
    is_prime[0] = is_prime[1] = False

    for p in range(2, int(N**0.5) + 1):
        if is_prime[p]:
            for k in range(p * p, N + 1, p * p):
                mu[k] = 0
            for k in range(p, N + 1, p):
                if mu[k] != 0 or k == p:
                    pass
            for k in range(p * p, N + 1, p):
                is_prime[k] = False

    # Reconstruction propre de μ
    mu2 = np.ones(N + 1, dtype=np.int8)
    mu2[0] = 0
    smallest_prime = np.zeros(N + 1, dtype=np.int32)

    for p in range(2, N + 1):
        if is_prime[p]:
            # Marquer les multiples de p² comme 0
            for k in range(p * p, N + 1, p * p):
                mu2[k] = 0
            # Compter les facteurs premiers (flip du signe)
            for k in range(p, N + 1, p):
                if mu2[k] != 0:
                    mu2[k] = -mu2[k]

    return mu2

def divisors(q, primes):
    """Retourne tous les diviseurs de q (primoriel)."""
    divs = [1]
    for p in primes:
        new_divs = []
        for d in divs:
            new_divs.append(d)
            new_divs.append(d * p)
        divs = new_divs
    return sorted(divs)

def mobius_value(d, primes):
    """μ(d) pour d diviseur d'un primoriel (squarefree)."""
    # d est squarefree (diviseur d'un primoriel)
    count = 0
    for p in primes:
        if d % p == 0:
            count += 1
    return (-1) ** count

# ═══════════════════════════════════════════════════════════
# §2. Calcul de S_d(q) et décomposition Route C
# ═══════════════════════════════════════════════════════════

def compute_route_C(q, primes, N_max=None):
    """
    Décomposition Route C pour le primoriel q.

    Calcule :
      S_d(q) = Σ_{n≤q, d|n} M(n)²  pour tout d | q
      κ(q)² = (1/φ(q)) Σ_{d|q} μ(d) S_d(q)

    Compare au terme principal de Titchmarsh :
      S_1(q) ~ q²/(2π²)
    """
    if N_max is None:
        N_max = q

    phi_q = euler_phi(q, primes)
    n_primes = len(primes)

    print(f"\n  q = {q:,}, φ(q) = {phi_q:,}, ω(q) = {n_primes}")

    # Crible de Möbius
    mu = mobius_sieve(N_max)
    M = np.cumsum(mu[:N_max + 1])  # M(n) = Σ_{k≤n} μ(k)

    # ─── κ(q) direct ───
    kappa_sq_direct = 0.0
    count_coprime = 0
    for a in range(1, min(q + 1, N_max + 1)):
        if gcd(a, q) == 1:
            kappa_sq_direct += M[a] ** 2
            count_coprime += 1

    kappa_sq_direct /= phi_q
    kappa_direct = np.sqrt(kappa_sq_direct)

    # ─── S_d(q) pour chaque d | q ───
    divs = divisors(q, primes)
    S_d = {}

    for d in divs:
        s = 0.0
        for n in range(d, min(q + 1, N_max + 1), d):
            s += M[n] ** 2
        S_d[d] = s

    # ─── Somme d'inclusion-exclusion ───
    ie_sum = 0.0
    ie_terms = {}
    for d in divs:
        mu_d = mobius_value(d, primes)
        term = mu_d * S_d[d]
        ie_terms[d] = (mu_d, S_d[d], term)
        ie_sum += term

    kappa_sq_ie = ie_sum / phi_q

    # ─── Prédiction Titchmarsh ───
    # S_1(q) ~ q²/(2π²) (conditionnel RH+LI, mais borne Ω incond.)
    titchmarsh_pred = q ** 2 / (2 * pi ** 2)

    # Ratio S_1 / prédiction
    ratio_S1 = S_d[1] / titchmarsh_pred if titchmarsh_pred > 0 else 0

    # ─── Erreur relative de la somme d'IE ───
    # Termes d ≥ 2
    error_sum = sum(abs(ie_terms[d][2]) for d in divs if d >= 2)
    principal_term = abs(ie_terms[1][2])

    error_ratio = error_sum / principal_term if principal_term > 0 else float('inf')

    # ─── σ_{-2}(q) = Π_{p|q}(1 + p⁻²) ───
    sigma_minus2 = 1.0
    for p in primes:
        sigma_minus2 *= (1 + 1.0 / p ** 2)

    # ─── Prédiction Route C pour κ² ───
    # κ² ~ q / (2π² · Π(1-1/p)) = q·e^γ·log(p_k) / (2π²) asymptotiquement
    prod_1_minus_1p = 1.0
    for p in primes:
        prod_1_minus_1p *= (1 - 1.0 / p)

    route_C_pred = q / (2 * pi ** 2 * prod_1_minus_1p) if prod_1_minus_1p > 0 else 0

    return {
        'q': q,
        'phi_q': phi_q,
        'n_primes': n_primes,
        'kappa_direct': kappa_direct,
        'kappa_sq_direct': kappa_sq_direct,
        'kappa_sq_ie': kappa_sq_ie,
        'S_d': S_d,
        'ie_terms': ie_terms,
        'S1': S_d[1],
        'titchmarsh_pred': titchmarsh_pred,
        'ratio_S1': ratio_S1,
        'error_sum': error_sum,
        'principal_term': principal_term,
        'error_ratio': error_ratio,
        'sigma_minus2': sigma_minus2,
        'route_C_pred': route_C_pred,
        'divs': divs,
    }

# ═══════════════════════════════════════════════════════════
# §3. Main
# ═══════════════════════════════════════════════════════════

def main():
    print("=" * 76)
    print("  ROUTE C — DÉCOMPOSITION DE TITCHMARSH DU VERROU κ")
    print("  κ(q)² = (1/φ(q)) Σ_{d|q} μ(d) S_d(q)")
    print("  Terme principal : S₁(q) ~ q²/(2π²)")
    print("  Dédié à Bernard Couret (1928–1999)")
    print("=" * 76)

    results = []

    # Tour primoriale : q₁ à q₇ (q₈ si mémoire ok)
    for k in range(1, 8):
        q, primes = primorial(k)
        if q > 600_000:
            print(f"\n  q = {q:,} trop grand pour crible complet, skip")
            break
        r = compute_route_C(q, primes)
        results.append(r)

    # ─── Tableau 1 : κ direct vs IE vs Route C ───
    print("\n" + "─" * 76)
    print("  TABLEAU 1 — κ(q) : direct vs inclusion-exclusion vs Route C")
    print("─" * 76)
    print(f"  {'q':>8}  {'κ direct':>10}  {'κ² direct':>12}  {'κ² IE':>12}  "
          f"{'κ² Route C':>12}  {'IE/dir':>8}")
    print("  " + "─" * 68)

    for r in results:
        ie_check = r['kappa_sq_ie'] / r['kappa_sq_direct'] if r['kappa_sq_direct'] > 0 else 0
        print(f"  {r['q']:>8,}  {r['kappa_direct']:>10.4f}  "
              f"{r['kappa_sq_direct']:>12.4f}  {r['kappa_sq_ie']:>12.4f}  "
              f"{r['route_C_pred']:>12.4f}  {ie_check:>8.4f}")

    # ─── Tableau 2 : S₁ vs Titchmarsh ───
    print("\n" + "─" * 76)
    print("  TABLEAU 2 — S₁(q) vs prédiction de Titchmarsh q²/(2π²)")
    print("─" * 76)
    print(f"  {'q':>8}  {'S₁(q)':>14}  {'q²/(2π²)':>14}  {'ratio':>8}  {'σ₋₂(q)':>8}")
    print("  " + "─" * 56)

    for r in results:
        print(f"  {r['q']:>8,}  {r['S1']:>14.2f}  {r['titchmarsh_pred']:>14.2f}  "
              f"{r['ratio_S1']:>8.4f}  {r['sigma_minus2']:>8.4f}")

    # ─── Tableau 3 : Domination du terme principal ───
    print("\n" + "─" * 76)
    print("  TABLEAU 3 — Domination : |erreur| / |terme principal|")
    print("  erreur = Σ_{d≥2} |μ(d) S_d(q)|,  principal = |S₁(q)|")
    print("─" * 76)
    print(f"  {'q':>8}  {'|principal|':>14}  {'|erreur|':>14}  {'ratio':>8}  {'dominant?':>10}")
    print("  " + "─" * 58)

    for r in results:
        dominant = "✅ OUI" if r['error_ratio'] < 1 else "❌ NON"
        print(f"  {r['q']:>8,}  {r['principal_term']:>14.2f}  "
              f"{r['error_sum']:>14.2f}  {r['error_ratio']:>8.4f}  {dominant:>10}")

    # ─── Tableau 4 : Détail des termes IE pour le plus grand q ───
    if results:
        r = results[-1]
        print(f"\n" + "─" * 76)
        print(f"  TABLEAU 4 — Détail inclusion-exclusion pour q = {r['q']:,}")
        print("─" * 76)
        print(f"  {'d':>8}  {'μ(d)':>5}  {'S_d(q)':>14}  {'μ(d)·S_d':>14}  {'% du total':>10}")
        print("  " + "─" * 55)

        total = sum(abs(v[2]) for v in r['ie_terms'].values())
        # Trier par |contribution| décroissante
        sorted_terms = sorted(r['ie_terms'].items(),
                              key=lambda x: -abs(x[1][2]))

        for d, (mu_d, sd, term) in sorted_terms[:20]:
            pct = abs(term) / total * 100 if total > 0 else 0
            print(f"  {d:>8,}  {mu_d:>5}  {sd:>14.2f}  {term:>14.2f}  {pct:>9.2f}%")

    # ─── Régression log κ vs log q ───
    if len(results) >= 3:
        print("\n" + "─" * 76)
        print("  RÉGRESSION : log κ = α · log q + β")
        print("─" * 76)

        log_q = np.array([log(r['q']) for r in results if r['kappa_direct'] > 0])
        log_k = np.array([log(r['kappa_direct']) for r in results if r['kappa_direct'] > 0])

        if len(log_q) >= 2:
            coeffs = np.polyfit(log_q, log_k, 1)
            alpha, beta = coeffs

            print(f"  α = {alpha:.4f}  (exposant de croissance)")
            print(f"  β = {beta:.4f}")

            # R²
            fitted = alpha * log_q + beta
            ss_res = np.sum((log_k - fitted) ** 2)
            ss_tot = np.sum((log_k - np.mean(log_k)) ** 2)
            r_squared = 1 - ss_res / ss_tot if ss_tot > 0 else 0

            print(f"  R² = {r_squared:.4f}")
            print(f"  Interprétation : κ ~ q^{alpha:.3f}")

    # ─── Verdict ───
    print("\n" + "=" * 76)
    print("  VERDICT ROUTE C")
    print("=" * 76)

    if results:
        last = results[-1]

        print(f"\n  Dernier niveau testé : q = {last['q']:,}")
        print(f"  κ(q) = {last['kappa_direct']:.4f}")
        print(f"  κ²(q) = {last['kappa_sq_direct']:.4f}")

        if last['error_ratio'] < 1:
            print(f"\n  ✅ S₁(q) DOMINE les termes d'erreur (ratio = {last['error_ratio']:.4f})")
            print("  La Route C est viable : κ(q) ≥ λ > 0 est soutenu")
        else:
            print(f"\n  ⚠ S₁(q) ne domine pas encore (ratio = {last['error_ratio']:.4f})")
            print("  La Route C nécessite des niveaux plus élevés")

        # κ croissant ?
        if len(results) >= 2:
            kappas = [r['kappa_direct'] for r in results]
            monotone = all(kappas[i] < kappas[i+1] for i in range(len(kappas)-1))
            print(f"\n  κ croissant le long de la tour : {'✅ OUI' if monotone else '⚠ NON'}")

        print(f"\n  Prédiction Route C (terme principal) :")
        print(f"    κ² ~ q / (2π² · Π(1-1/p)) = {last['route_C_pred']:.4f}")
        print(f"    κ² observé                 = {last['kappa_sq_direct']:.4f}")
        if last['route_C_pred'] > 0:
            print(f"    ratio observé/prédit       = {last['kappa_sq_direct']/last['route_C_pred']:.4f}")

    print(f"\n  RHClaimed = false")
    print("  « Le noyau fini est exact ; le pont global reste ouvert. »")
    print("=" * 76)

if __name__ == "__main__":
    main()
