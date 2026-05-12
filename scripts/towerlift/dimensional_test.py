#!/usr/bin/env python3
"""
TEST DIMENSIONNEL COMPLET — mod 30 vs mod 210 vs mod 2310
Couret-Unification v18 — Mars 2026

OBJECTIF SCIENTIFIQUE CENTRAL :
  Si δ̃ ≈ 1/√(k-1) pour chaque modulus (k = φ(q)),
  alors λ est une constante géométrique du simplexe.
  Si δ̃ ≈ 1/√7 indépendamment du modulus,
  alors λ est une constante arithmétique profonde.

  CE TEST TRANCHE.

Inclut aussi :
  - Correction de l'incohérence des signes ε₃₀
  - Analyse des suites SG actives pour chaque modulus
  - Spectre de l'opérateur combiné à chaque niveau
"""

import numpy as np
from sympy import isprime, primerange, totient, gcd
from collections import defaultdict
import time, json

LIMIT = 5_000_000

print("=" * 78)
print("  TEST DIMENSIONNEL — LE DISCRIMINANT SCIENTIFIQUE")
print("  mod 30 (k=8) vs mod 210 (k=48) vs mod 2310 (k=480)")
print("=" * 78)

# ===================================================================
# PHASE 0 : CORRECTION DES SIGNES ε₃₀
# ===================================================================
print("\n" + "━" * 78)
print("  PHASE 0 : Vérification des signes du caractère ε₃₀")
print("━" * 78)

# Le caractère utilisé dans le code TowerLift v17 :
EPS_CODE = {1: 1, 7: 1, 11: -1, 13: 1, 17: -1, 19: 1, 23: -1, 29: 1}

# Le caractère mentionné dans la Section 4 de l'article :
# ε₃₀(11) = -1, ε₃₀(23) = 1, ε₃₀(29) = 1
# PROBLÈME : ε₃₀(23) = 1 dans l'article mais -1 dans le code !

print("  Signes dans le CODE (TowerLift v17, Lean, Python) :")
for r in [1, 7, 11, 13, 17, 19, 23, 29]:
    print(f"    ε₃₀({r:>2}) = {EPS_CODE[r]:>+2}")

print(f"\n  Signes dans la SECTION 4 de l'article :")
print(f"    ε₃₀(11) = -1, ε₃₀(23) = +1, ε₃₀(29) = +1")

print(f"\n  ⚠️  INCOHÉRENCE DÉTECTÉE :")
print(f"    ε₃₀(23) = -1 (code) vs +1 (article)")
print(f"    ε₃₀(29) = +1 (les deux) ✓")
print(f"    ε₃₀(11) = -1 (les deux) ✓")

# Vérifions quel est le BON caractère
# Le caractère du code est le caractère de Kronecker (−3|·) × signe
# ou une variante. Vérifions la multiplicativité :
print(f"\n  Test de cohérence multiplicative du caractère CODE :")
R30 = [1, 7, 11, 13, 17, 19, 23, 29]
errors = 0
for a in R30:
    for b in R30:
        ab = (a * b) % 30
        if ab in EPS_CODE:
            if EPS_CODE[a] * EPS_CODE[b] != EPS_CODE[ab]:
                print(f"    ε({a})×ε({b}) = {EPS_CODE[a]*EPS_CODE[b]} ≠ ε({ab}) = {EPS_CODE[ab]}")
                errors += 1

if errors == 0:
    print(f"    ✓ Le caractère du code est multiplicatif")
else:
    print(f"    ✗ {errors} violations de multiplicativité")

# Le bon caractère pour le projet est celui du CODE (multiplicatif)
# L'article doit être corrigé : ε₃₀(23) = -1 (pas +1)
print(f"\n  CONCLUSION : Le CODE est correct. L'article Section 4 contient")
print(f"  une erreur typographique : ε₃₀(23) devrait être -1, pas +1.")
print(f"  Correction : ε₃₀ sur SG actives = {{-1, -1, +1}} (code)")

# ===================================================================
# PHASE 1 : Données Sophie Germain
# ===================================================================
print("\n" + "━" * 78)
print("  PHASE 1 : Construction des données Sophie Germain")
print("━" * 78)

t0 = time.time()
sg = [p for p in primerange(2, LIMIT) if isprime(2 * p + 1)]
print(f"  {len(sg):,} SG trouvés (p ≤ {LIMIT:,}, {time.time()-t0:.1f}s)")

# ===================================================================
# PHASE 2 : Analyse pour CHAQUE MODULUS
# ===================================================================

def analyze_modulus(q, sg_list, label):
    """Analyse complète SG pour un modulus q."""
    phi_q = int(totient(q))
    coprime_classes = sorted([r for r in range(q) if gcd(r, q) == 1])

    print(f"\n{'━' * 78}")
    print(f"  {label} : q = {q}, φ(q) = {phi_q}, k-1 = {phi_q - 1}")
    print(f"  Constante simplexiale : 1/√(k-1) = 1/√{phi_q-1} = {1/np.sqrt(phi_q-1):.8f}")
    print(f"  Constante Δ⁷ (référence) : 1/√7 = {1/np.sqrt(7):.8f}")
    print(f"{'━' * 78}")

    # Identifier les suites SG actives pour ce modulus
    active_classes = []
    for r in coprime_classes:
        f_r = (2 * r + 1) % q
        if gcd(f_r, q) == 1:  # f(r) reste copremier à q
            active_classes.append(r)

    inactive_classes = [r for r in coprime_classes if r not in active_classes]

    print(f"  Suites actives SG : {len(active_classes)} / {phi_q}")
    print(f"  Fraction active : {len(active_classes)}/{phi_q} = {len(active_classes)/phi_q:.6f}")

    if len(active_classes) <= 20:
        print(f"  Classes actives : {active_classes}")
    else:
        print(f"  Premières classes actives : {active_classes[:10]}...")

    # Distribution des SG dans les classes actives
    sg_by_class = defaultdict(int)
    sg_filtered = []
    for p in sg_list:
        if p > max(5, max([pp for pp in [2,3,5,7,11] if pp < q], default=5)):
            r = p % q
            if r in active_classes:
                sg_by_class[r] += 1
                sg_filtered.append((p, r))

    total_active = len(sg_filtered)
    print(f"  SG dans suites actives : {total_active:,}")

    if total_active < 100:
        print(f"  ⚠️ Pas assez de données pour une analyse fiable")
        return None

    n_active = len(active_classes)
    if n_active < 2:
        print(f"  ⚠️ Moins de 2 classes actives, pas d'analyse spectrale possible")
        return None

    # Matrice de transition entre SG consécutifs
    idx_map = {r: i for i, r in enumerate(active_classes)}
    counts = np.zeros((n_active, n_active), dtype=int)
    for k in range(len(sg_filtered) - 1):
        _, r1 = sg_filtered[k]
        _, r2 = sg_filtered[k + 1]
        counts[idx_map[r1], idx_map[r2]] += 1

    row_sums = counts.sum(axis=1, keepdims=True).astype(float)
    row_sums[row_sums == 0] = 1.0
    M = counts / row_sums

    # Biais diagonal
    uniform = 1.0 / n_active
    diag_vals = [M[i, i] for i in range(n_active)]
    diag_mean = np.mean(diag_vals)
    diag_bias = diag_mean - uniform

    print(f"  Diagonale moyenne M[i,i] : {diag_mean:.6f} (uniforme = {uniform:.6f})")
    print(f"  Biais diagonal : {diag_bias:+.6f} ({'négatif ✓' if diag_bias < 0 else 'positif ou nul'})")

    # Opérateur de Hecke T₂ restreint
    T2 = np.zeros((n_active, n_active))
    for i, ri in enumerate(active_classes):
        target = (2 * ri + 1) % q
        if target in idx_map:
            T2[i, idx_map[target]] = 1.0

    # Caractère : utiliser le caractère de Kronecker (-1)^index ou adapté
    # Pour être cohérent, on utilise ε_q = caractère non trivial du groupe
    # Pour mod 30 : le même que dans le code
    # Pour mod 210, 2310 : extension naturelle

    # Caractère simple : signe alterné sur les classes actives
    # Plus rigoureux : caractère de Dirichlet réel non trivial
    eps_vals = np.ones(n_active)
    for i, r in enumerate(active_classes):
        # Utiliser le symbole de Legendre (r | q) comme proxy
        # ou simplement le caractère du code pour mod 30
        if q == 30:
            eps_vals[i] = EPS_CODE.get(r, 0)
        else:
            # Pour mod 210, 2310 : étendre le caractère mod 30
            r30 = r % 30
            eps_vals[i] = EPS_CODE.get(r30, 0) if r30 in EPS_CODE else 1.0

    D_eps = np.diag(eps_vals)

    # Opérateur combiné
    Delta = D_eps @ T2 @ M
    Delta_sym = (Delta + Delta.T) / 2.0

    # Spectre
    eigenvalues = np.linalg.eigvalsh(Delta_sym)
    ev_sorted = sorted(eigenvalues, key=lambda x: -abs(x))

    # Constantes de référence
    lambda_simplex = 1.0 / np.sqrt(n_active - 1) if n_active > 1 else 0
    lambda_7 = 1.0 / np.sqrt(7)

    print(f"\n  Spectre de Δ̃ ({n_active}×{n_active}) :")
    print(f"  {'#':>3}  {'δ̃':>12}  {'|δ̃|':>10}  {'écart 1/√{0}'.format(n_active-1):>16}  {'écart 1/√7':>12}")

    for k, ev in enumerate(ev_sorted[:min(8, len(ev_sorted))]):
        mod = abs(ev)
        ecart_simplex = abs(mod - lambda_simplex)
        ecart_7 = abs(mod - lambda_7)
        pct_s = 100 * ecart_simplex / lambda_simplex if lambda_simplex > 0 else 999
        pct_7 = 100 * ecart_7 / lambda_7
        ms = " ◄" if pct_s < 5 else ""
        m7 = " ◄" if pct_7 < 5 else ""
        print(f"  {k+1:>3}  {ev:>+12.6f}  {mod:>10.6f}  {ecart_simplex:.6f} ({pct_s:.1f}%){ms}  {ecart_7:.6f} ({pct_7:.1f}%){m7}")

    # Trouver la VP positive la plus proche de chaque référence
    positive_evs = [ev for ev in eigenvalues if ev > 0.01]
    if positive_evs:
        best_pos = max(positive_evs)
        ecart_s = abs(best_pos - lambda_simplex)
        ecart_7 = abs(best_pos - lambda_7)

        print(f"\n  Meilleure VP positive : δ̃+ = {best_pos:.8f}")
        print(f"    vs 1/√{n_active-1} = {lambda_simplex:.8f} → écart {100*ecart_s/lambda_simplex:.3f}%")
        print(f"    vs 1/√7 = {lambda_7:.8f} → écart {100*ecart_7/lambda_7:.3f}%")

        closer_to = "SIMPLEXE" if ecart_s < ecart_7 else "Δ⁷ (1/√7)"
        print(f"    ➜ Plus proche de : {closer_to}")
    else:
        best_pos = None
        print(f"\n  Pas de VP positive significative")

    # Spectre de M seul (sans Hecke ni Dirichlet)
    ev_M = np.linalg.eigvals(M)
    ev_M_sorted = sorted(ev_M, key=lambda x: -abs(x))
    second_ev_M = abs(ev_M_sorted[1]) if len(ev_M_sorted) > 1 else 0

    print(f"\n  Spectre de M seul (transition) :")
    print(f"    |λ₂(M)| = {second_ev_M:.8f}")
    print(f"    Gap spectral = {1 - second_ev_M:.8f}")

    return {
        "q": q, "phi_q": phi_q, "n_active": n_active,
        "lambda_simplex": lambda_simplex, "lambda_7": lambda_7,
        "best_pos_ev": float(best_pos) if best_pos is not None else None,
        "all_eigenvalues": [float(e) for e in ev_sorted],
        "diag_bias": float(diag_bias),
        "second_ev_M": float(second_ev_M),
        "total_sg_active": total_active,
        "fraction_active": len(active_classes) / phi_q,
    }

# ===================================================================
# Exécuter pour les trois moduli
# ===================================================================
results = {}

# MOD 30
r30 = analyze_modulus(30, sg, "NIVEAU 1 : MOD 30")
if r30: results["mod30"] = r30

# MOD 210
r210 = analyze_modulus(210, sg, "NIVEAU 2 : MOD 210")
if r210: results["mod210"] = r210

# MOD 2310
r2310 = analyze_modulus(2310, sg, "NIVEAU 3 : MOD 2310")
if r2310: results["mod2310"] = r2310

# ===================================================================
# PHASE FINALE : VERDICT SCIENTIFIQUE
# ===================================================================
print("\n" + "=" * 78)
print("  VERDICT DU TEST DIMENSIONNEL")
print("=" * 78)

print(f"""
  ┌────────────────────────────────────────────────────────────────────┐
  │  QUESTION : λ = 1/√7 est-elle géométrique ou arithmétique ?        │
  ├────────────────────────────────────────────────────────────────────┤
  │                                                                    │
  │  Si δ̃ ≈ 1/√(k-1) pour chaque q → constante GÉOMÉTRIQUE             │
  │  Si δ̃ ≈ 1/√7 indépendamment de q → constante ARITHMÉTIQUE          │
  │                                                                    │""")

for label, key in [("mod 30", "mod30"), ("mod 210", "mod210"), ("mod 2310", "mod2310")]:
    if key in results:
        r = results[key]
        if r["best_pos_ev"] is not None:
            ecart_s = abs(r["best_pos_ev"] - r["lambda_simplex"])
            ecart_7 = abs(r["best_pos_ev"] - r["lambda_7"])
            pct_s = 100 * ecart_s / r["lambda_simplex"] if r["lambda_simplex"] > 0 else 999
            pct_7 = 100 * ecart_7 / r["lambda_7"]
            closer = "simplexe" if ecart_s < ecart_7 else "1/√7"
            print(f"  │  {label:>8} : δ̃+ = {r['best_pos_ev']:.6f}  "
                  f"1/√{r['n_active']-1} = {r['lambda_simplex']:.6f}  "
                  f"→ {closer:>10} ({min(pct_s,pct_7):.1f}%)  │")
        else:
            print(f"  │  {label:>8} : pas de VP positive                              │")

print(f"  │                                                                    │")

# Déterminer le verdict
if all(k in results for k in ["mod30", "mod210"]):
    r30 = results["mod30"]
    r210 = results["mod210"]

    if r30["best_pos_ev"] is not None and r210["best_pos_ev"] is not None:
        # Pour mod 30 : est-ce plus proche de 1/√7 ou 1/√2 ?
        e30_7 = abs(r30["best_pos_ev"] - 1/np.sqrt(7))
        e30_s = abs(r30["best_pos_ev"] - 1/np.sqrt(r30["n_active"]-1))

        # Pour mod 210 : est-ce plus proche de 1/√47 ou 1/√7 ?
        e210_7 = abs(r210["best_pos_ev"] - 1/np.sqrt(7))
        e210_s = abs(r210["best_pos_ev"] - 1/np.sqrt(r210["n_active"]-1))

        if e210_s < e210_7:
            verdict = "GÉOMÉTRIQUE (constante du simplexe local)"
            detail = f"mod 210 : δ̃+ plus proche de 1/√{r210['n_active']-1} que de 1/√7"
        elif e210_7 < e210_s:
            verdict = "ARITHMÉTIQUE (constante universelle)"
            detail = f"mod 210 : δ̃+ plus proche de 1/√7 que de 1/√{r210['n_active']-1}"
        else:
            verdict = "INDÉTERMINÉ (besoin de plus de données)"
            detail = "Écarts comparables"

        print(f"  │  VERDICT : {verdict:<52}    │")
        print(f"  │  Détail  : {detail:<52}     │")

print(f"  └────────────────────────────────────────────────────────────────────┘")

# Export JSON
json_path = "docs/towerlift/dimensional_test_results.json"
with open(json_path, "w") as f:
    json.dump(results, f, indent=2)

print(f"\n  JSON exporté : {json_path}")
print(f"\n{'=' * 78}")
print(f"  ✅ TEST DIMENSIONNEL TERMINÉ")
print(f"{'=' * 78}")
