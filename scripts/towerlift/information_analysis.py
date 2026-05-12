#!/usr/bin/env python3
"""
ANALYSE INFORMATIONNELLE — VITESSE DE L'INFORMATION ARITHMÉTIQUE
Couret-Unification v19 — Mars 2026

HYPOTHÈSE :
  1/√7 est la vitesse caractéristique de propagation de l'information
  dans le "matériau" arithmétique défini par (Z/30Z)*.

TEST :
  Calculer I(p_n mod q ; p_{n+1} mod q) pour q = 30, 210, 2310
  Si I se stabilise autour d'une valeur liée à λ² = 1/7,
  l'interprétation informationnelle est confirmée.

MÉTRIQUES :
  1. Mutual Information I(X;Y) entre résidus consécutifs
  2. Information de Fisher sur le simplexe
  3. Entropie de transfert T(X→Y)
  4. Capacité effective du canal SG
  5. Corrélation informationnelle normalisée
"""

import numpy as np
from sympy import isprime, primerange, totient
from collections import defaultdict
from math import gcd, log, log2, sqrt
import time, json

LIMIT = 5_000_000
LAMBDA = 1 / sqrt(7)
LAMBDA_SQ = 1.0 / 7.0

print("=" * 78)
print("  ANALYSE INFORMATIONNELLE — VITESSE DE L'INFORMATION SG")
print("  Hypothèse : 1/√7 = vitesse caractéristique du canal mod 30")
print("=" * 78)

# ===================================================================
# Données SG
# ===================================================================
t0 = time.time()
sg = [p for p in primerange(2, LIMIT) if isprime(2 * p + 1)]
sg = [p for p in sg if p > 11]  # Filtrer les petits
print(f"\n[1] {len(sg):,} SG (p > 11, p ≤ {LIMIT:,}, {time.time()-t0:.1f}s)")

# ===================================================================
# Fonctions d'information
# ===================================================================

def entropy(probs):
    """Entropie de Shannon H(X) = -Σ p_i log p_i."""
    return -sum(p * log(p) for p in probs if p > 0)

def entropy_bits(probs):
    """Entropie en bits."""
    return -sum(p * log2(p) for p in probs if p > 0)

def mutual_information(joint, marginal_x, marginal_y):
    """I(X;Y) = Σ p(x,y) log(p(x,y) / (p(x)p(y)))."""
    mi = 0.0
    for (x, y), pxy in joint.items():
        if pxy > 0:
            px = marginal_x.get(x, 0)
            py = marginal_y.get(y, 0)
            if px > 0 and py > 0:
                mi += pxy * log(pxy / (px * py))
    return mi

def transfer_entropy(data, classes):
    """T(X→Y) = H(Y|Y_past) - H(Y|Y_past, X_past)
    Approximé par T ≈ I(X_n; Y_{n+1} | Y_n)."""
    # Simplification : calculer I(X_n; X_{n+2} | X_{n+1})
    # via la chaîne X_n → X_{n+1} → X_{n+2}
    idx = {c: i for i, c in enumerate(classes)}
    n_classes = len(classes)

    # Trigrammes
    trigram_counts = defaultdict(int)
    bigram_counts_12 = defaultdict(int)
    bigram_counts_23 = defaultdict(int)
    unigram_counts = defaultdict(int)

    for k in range(len(data) - 2):
        r1 = data[k]
        r2 = data[k + 1]
        r3 = data[k + 2]
        trigram_counts[(r1, r2, r3)] += 1
        bigram_counts_12[(r1, r2)] += 1
        bigram_counts_23[(r2, r3)] += 1
        unigram_counts[r2] += 1

    total = sum(trigram_counts.values())
    if total == 0:
        return 0.0

    # T(X→Y) = Σ p(x_n, x_{n+1}, x_{n+2}) log [p(x_{n+2}|x_{n+1},x_n) / p(x_{n+2}|x_{n+1})]
    te = 0.0
    for (r1, r2, r3), count in trigram_counts.items():
        p_trigram = count / total
        p_bigram_12 = bigram_counts_12.get((r1, r2), 0) / total
        p_bigram_23 = bigram_counts_23.get((r2, r3), 0) / total
        p_uni_2 = unigram_counts.get(r2, 0) / total

        if p_bigram_12 > 0 and p_bigram_23 > 0 and p_uni_2 > 0:
            # p(x3|x2,x1) = p(x1,x2,x3) / p(x1,x2)
            p_cond_full = count / bigram_counts_12.get((r1, r2), 1)
            # p(x3|x2) = p(x2,x3) / p(x2)
            p_cond_markov = bigram_counts_23.get((r2, r3), 0) / unigram_counts.get(r2, 1)

            if p_cond_full > 0 and p_cond_markov > 0:
                te += p_trigram * log(p_cond_full / p_cond_markov)

    return te

# ===================================================================
# Analyse par modulus
# ===================================================================

def analyze_information(q, sg_list, label):
    """Analyse informationnelle complète pour un modulus q."""
    coprime = sorted([r for r in range(q) if gcd(r, q) == 1])
    phi_q = len(coprime)

    # Classes actives SG
    active = [r for r in coprime if gcd((2*r+1) % q, q) == 1]
    n_active = len(active)

    print(f"\n{'━' * 78}")
    print(f"  {label} : q = {q}, φ(q) = {phi_q}, n_active = {n_active}")
    print(f"{'━' * 78}")

    # Résidus des SG
    residus = [p % q for p in sg_list]

    # Filtrer sur classes actives
    residus_active = [r for r in residus if r in active]
    N = len(residus_active)
    print(f"  N = {N:,} SG dans classes actives")

    # === 1. Distribution marginale ===
    counts = defaultdict(int)
    for r in residus_active:
        counts[r] += 1

    marginal = {r: counts[r] / N for r in active}
    H_marginal = entropy(list(marginal.values()))
    H_bits = entropy_bits(list(marginal.values()))
    H_max = log(n_active)
    H_max_bits = log2(n_active)

    print(f"\n  1. ENTROPIE MARGINALE")
    print(f"     H(X) = {H_marginal:.6f} nats ({H_bits:.4f} bits)")
    print(f"     H_max = ln({n_active}) = {H_max:.6f} nats ({H_max_bits:.4f} bits)")
    print(f"     Efficacité H/H_max = {H_marginal/H_max:.6f}")

    # === 2. Distribution jointe (paires consécutives) ===
    joint_counts = defaultdict(int)
    for k in range(N - 1):
        joint_counts[(residus_active[k], residus_active[k+1])] += 1

    total_pairs = N - 1
    joint = {k: v / total_pairs for k, v in joint_counts.items()}

    # Marginales à partir de la jointe
    marginal_x = defaultdict(float)
    marginal_y = defaultdict(float)
    for (x, y), p in joint.items():
        marginal_x[x] += p
        marginal_y[y] += p

    # === 3. Mutual Information ===
    MI = mutual_information(joint, marginal_x, marginal_y)
    MI_bits = MI / log(2)

    # Normalisation : coefficient d'incertitude U = I(X;Y) / H(X)
    U = MI / H_marginal if H_marginal > 0 else 0

    # Normalized MI : NMI = 2·I(X;Y) / (H(X) + H(Y))
    H_Y = entropy(list(marginal_y.values()))
    NMI = 2 * MI / (H_marginal + H_Y) if (H_marginal + H_Y) > 0 else 0

    print(f"\n  2. MUTUAL INFORMATION I(X_n; X_{{n+1}})")
    print(f"     I = {MI:.8f} nats ({MI_bits:.6f} bits)")
    print(f"     U = I/H = {U:.8f} (coefficient d'incertitude)")
    print(f"     NMI = 2I/(H_X+H_Y) = {NMI:.8f}")

    # === 4. Comparaison avec λ² = 1/7 ===
    print(f"\n  3. COMPARAISON AVEC λ² = 1/7")
    print(f"     λ² = 1/7 = {LAMBDA_SQ:.8f}")
    print(f"     I(X;Y) = {MI:.8f}")
    print(f"     I/H_max = {MI/H_max:.8f}")

    # Ratio informationnel : quelle fraction de l'entropie max est "couplée" ?
    info_ratio = MI / H_max
    ecart_lambda_sq = abs(info_ratio - LAMBDA_SQ)
    ecart_pct = 100 * ecart_lambda_sq / LAMBDA_SQ
    print(f"     Écart |I/H_max - 1/7| = {ecart_lambda_sq:.8f} ({ecart_pct:.2f}%)")

    # Test U ≈ 1/7 ?
    ecart_U = abs(U - LAMBDA_SQ)
    ecart_U_pct = 100 * ecart_U / LAMBDA_SQ
    print(f"     Écart |U - 1/7| = {ecart_U:.8f} ({ecart_U_pct:.2f}%)")

    # Test NMI ≈ λ ?
    ecart_NMI_lambda = abs(NMI - LAMBDA)
    ecart_NMI_pct = 100 * ecart_NMI_lambda / LAMBDA
    print(f"     Écart |NMI - 1/√7| = {ecart_NMI_lambda:.8f} ({ecart_NMI_pct:.2f}%)")

    # === 5. Matrice de transition et entropie conditionnelle ===
    idx_map = {r: i for i, r in enumerate(active)}
    M = np.zeros((n_active, n_active))
    for (x, y), count in joint_counts.items():
        i, j = idx_map[x], idx_map[y]
        M[i, j] = count

    # Normaliser
    row_sums = M.sum(axis=1, keepdims=True)
    row_sums[row_sums == 0] = 1
    M = M / row_sums

    # Entropie conditionnelle H(Y|X) = H(X,Y) - H(X)
    H_joint = entropy([p for p in joint.values() if p > 0])
    H_cond = H_joint - H_marginal

    print(f"\n  4. ENTROPIE CONDITIONNELLE")
    print(f"     H(X,Y) = {H_joint:.6f} nats")
    print(f"     H(Y|X) = {H_cond:.6f} nats")
    print(f"     I(X;Y) = H(Y) - H(Y|X) = {H_Y - H_cond:.8f} (vérification)")

    # Fraction de prédictibilité
    predictability = 1 - H_cond / H_marginal if H_marginal > 0 else 0
    print(f"     Prédictibilité = 1 - H(Y|X)/H(Y) = {predictability:.8f}")
    print(f"     = fraction d'information transmise = {predictability:.6f}")

    # === 6. Transfer entropy ===
    TE = transfer_entropy(residus_active, active)
    print(f"\n  5. ENTROPIE DE TRANSFERT T(X_n → X_{{n+2}} | X_{{n+1}})")
    print(f"     T = {TE:.8f} nats ({TE/log(2):.6f} bits)")
    print(f"     Mémoire au-delà de Markov : {'significative' if TE > 0.001 else 'faible'}")

    # === 7. Capacité effective du canal ===
    # C = max I(X;Y) sur toutes les distributions d'entrée
    # Pour un canal symétrique, C = log(k) - H(ligne de M)
    avg_row_entropy = np.mean([entropy(M[i][M[i] > 0]) for i in range(n_active)])
    capacity = log(n_active) - avg_row_entropy
    capacity_bits = capacity / log(2)

    print(f"\n  6. CAPACITÉ DU CANAL SG")
    print(f"     C = {capacity:.8f} nats ({capacity_bits:.6f} bits)")
    print(f"     C/log(n) = {capacity/log(n_active):.8f}")
    print(f"     Écart |C/log(n) - 1/7| = {abs(capacity/log(n_active) - LAMBDA_SQ):.8f}")

    # === 8. Information de Fisher ===
    # I_F = Σ_i (dp_i/dθ)² / p_i pour le modèle multinomial
    # Au centre uniforme : I_F = n_active
    # La "vitesse" sur le simplexe : v = 1/√I_F_effective

    # Information de Fisher empirique via les fluctuations
    props = np.array([marginal.get(r, 0) for r in active])
    props_uniform = np.ones(n_active) / n_active
    delta_p = props - props_uniform

    # I_F ≈ Σ (δp_i)² / p_i_uniform = n_active × Σ (δp_i)²
    fisher_empirical = n_active * np.sum(delta_p**2)

    print(f"\n  7. INFORMATION DE FISHER")
    print(f"     I_F théorique (uniforme) = {n_active}")
    print(f"     I_F empirique (fluctuations) = {fisher_empirical:.8f}")
    print(f"     Vitesse = 1/√I_F_emp = {1/sqrt(fisher_empirical) if fisher_empirical > 0 else 'inf'}")

    # === 9. Spectre informationnel ===
    eigenvalues = np.linalg.eigvals(M)
    ev_sorted = sorted(eigenvalues, key=lambda x: -abs(x))

    # Le gap spectral est lié au taux de convergence = "vitesse de dissipation"
    lambda2 = abs(ev_sorted[1]) if len(ev_sorted) > 1 else 0
    gap = 1 - lambda2
    mixing_time = 1 / gap if gap > 0 else float('inf')

    # La "vitesse informationnelle" v = gap / dimension_effective
    v_info = gap / (n_active - 1) if n_active > 1 else 0

    print(f"\n  8. VITESSE INFORMATIONNELLE")
    print(f"     |λ₂(M)| = {lambda2:.8f}")
    print(f"     Gap spectral g = {gap:.8f}")
    print(f"     Temps de mélange ≈ {mixing_time:.2f}")
    print(f"     Vitesse v = g/(n-1) = {v_info:.8f}")
    print(f"     √v = {sqrt(v_info) if v_info > 0 else 0:.8f}")
    print(f"     Écart |√v - 1/√7| = {abs(sqrt(v_info) - LAMBDA):.8f}")

    # === 10. Synthèse ===
    print(f"\n  9. SYNTHÈSE INFORMATIONNELLE")

    metrics = {
        "I/H_max": MI / H_max,
        "U = I/H": U,
        "NMI": NMI,
        "C/log(n)": capacity / log(n_active),
        "predictability": predictability,
        "√(g/(n-1))": sqrt(v_info) if v_info > 0 else 0,
    }

    print(f"     {'Métrique':>20}  {'Valeur':>10}  {'1/7':>8}  {'1/√7':>8}  {'Meilleur':>10}")
    print(f"     {'─'*20}  {'─'*10}  {'─'*8}  {'─'*8}  {'─'*10}")

    for name, val in metrics.items():
        e7 = abs(val - LAMBDA_SQ)
        esqrt7 = abs(val - LAMBDA)
        best = "1/7" if e7 < esqrt7 else "1/√7"
        best_pct = min(e7/LAMBDA_SQ, esqrt7/LAMBDA) * 100
        print(f"     {name:>20}  {val:>10.6f}  {e7:>8.5f}  {esqrt7:>8.5f}  {best:>6} ({best_pct:.1f}%)")

    return {
        "q": q, "n_active": n_active, "N": N,
        "H_marginal": H_marginal, "H_max": H_max,
        "MI": MI, "MI_bits": MI_bits,
        "U": U, "NMI": NMI,
        "predictability": predictability,
        "transfer_entropy": TE,
        "capacity": capacity,
        "fisher_empirical": fisher_empirical,
        "lambda2_M": lambda2, "gap": gap, "v_info": v_info,
        "metrics": {k: float(v) for k, v in metrics.items()},
    }

# ===================================================================
# Exécuter
# ===================================================================
results = {}
for q, label in [(30, "MOD 30"), (210, "MOD 210"), (2310, "MOD 2310")]:
    r = analyze_information(q, sg, label)
    if r:
        results[f"mod{q}"] = r

# ===================================================================
# TABLEAU FINAL — STABILITÉ DE L'INFORMATION
# ===================================================================
print("\n" + "=" * 78)
print("  VERDICT INFORMATIONNEL — STABILITÉ SOUS LIFT")
print("=" * 78)

key_metrics = ["I/H_max", "U = I/H", "NMI", "C/log(n)", "predictability", "√(g/(n-1))"]

print(f"\n  {'Métrique':>20}  {'mod 30':>10}  {'mod 210':>10}  {'mod 2310':>10}  {'1/7':>8}  {'1/√7':>8}  {'Stable?':>8}")
print(f"  {'─'*20}  {'─'*10}  {'─'*10}  {'─'*10}  {'─'*8}  {'─'*8}  {'─'*8}")

for metric in key_metrics:
    vals = []
    for key in ["mod30", "mod210", "mod2310"]:
        if key in results and metric in results[key]["metrics"]:
            vals.append(results[key]["metrics"][metric])
        else:
            vals.append(None)

    v_strs = [f"{v:.6f}" if v is not None else "N/A" for v in vals]

    # Stabilité = faible variation entre moduli
    valid_vals = [v for v in vals if v is not None]
    if len(valid_vals) >= 2:
        cv = np.std(valid_vals) / abs(np.mean(valid_vals)) if np.mean(valid_vals) != 0 else float('inf')
        stable = "✓" if cv < 0.3 else "~" if cv < 1.0 else "✗"
    else:
        stable = "?"

    print(f"  {metric:>20}  {v_strs[0]:>10}  {v_strs[1]:>10}  {v_strs[2]:>10}  {LAMBDA_SQ:>8.5f}  {LAMBDA:>8.5f}  {stable:>8}")

# Verdict
print(f"\n  ┌──────────────────────────────────────────────────────────────────┐")
print(f"  │  HYPOTHÈSE : 1/√7 = vitesse de l'information arithmétique        │")
print(f"  ├──────────────────────────────────────────────────────────────────┤")

# Chercher la métrique la plus stable et la plus proche de 1/7 ou 1/√7
best_metric = None
best_stability = float('inf')
best_proximity = float('inf')

for metric in key_metrics:
    valid = []
    for key in ["mod30", "mod210", "mod2310"]:
        if key in results and metric in results[key]["metrics"]:
            valid.append(results[key]["metrics"][metric])

    if len(valid) >= 2:
        mean_val = np.mean(valid)
        cv = np.std(valid) / abs(mean_val) if mean_val != 0 else float('inf')
        prox_7 = abs(mean_val - LAMBDA_SQ) / LAMBDA_SQ
        prox_sqrt7 = abs(mean_val - LAMBDA) / LAMBDA
        prox = min(prox_7, prox_sqrt7)

        score = cv + prox  # Plus bas = mieux
        if score < best_stability + best_proximity:
            best_stability = cv
            best_proximity = prox
            best_metric = metric

if best_metric:
    vals_best = [results[k]["metrics"][best_metric] for k in ["mod30", "mod210", "mod2310"] if k in results]
    mean_best = np.mean(vals_best)

    e7 = abs(mean_best - LAMBDA_SQ)
    esqrt7 = abs(mean_best - LAMBDA)
    target = "1/7" if e7 < esqrt7 else "1/√7"
    target_val = LAMBDA_SQ if e7 < esqrt7 else LAMBDA

    print(f"  │  Métrique la plus stable : {best_metric:<36}  │")
    print(f"  │  Valeur moyenne : {mean_best:.6f}  (cible {target} = {target_val:.6f})              │")
    print(f"  │  Stabilité (CV) : {best_stability:.4f}                                         │")
    print(f"  │  Proximité : {100*min(e7/LAMBDA_SQ, esqrt7/LAMBDA):.1f}%                                               │")

print(f"  └──────────────────────────────────────────────────────────────────┘")

# Export
json_path = "docs/towerlift/information_analysis.json"
with open(json_path, "w") as f:
    json.dump(results, f, indent=2, default=str)

print(f"\n  JSON : {json_path}")
print(f"\n{'=' * 78}")
print(f"  ✅ ANALYSE INFORMATIONNELLE TERMINÉE")
print(f"{'=' * 78}")
