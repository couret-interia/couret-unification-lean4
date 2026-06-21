#!/usr/bin/env python3
"""
Analyse Spectrale des Chaînes de Sophie Germain modulo 30
Projet Couret-Unification — Mars 2026

Objectif : Construire la matrice de transition 8×8 des chaînes de Sophie Germain
dans les classes résiduelles mod 30, calculer le spectre, et tester la
proximité avec λ = 1/√7 ≈ 0.37796.
"""

import numpy as np
from sympy import isprime, primerange
from collections import defaultdict
from datetime import datetime
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import json
import time

# ============================================================================
# CONFIGURATION
# ============================================================================
LIMIT = 2_000_000          # Limite supérieure pour la recherche
RESIDUES = [1, 7, 11, 13, 17, 19, 23, 29]  # Classes copremieres mod 30
LAMBDA_TARGET = 1 / np.sqrt(7)  # ≈ 0.37796
RES_TO_IDX = {r: i for i, r in enumerate(RESIDUES)}

print("=" * 70)
print("  ANALYSE SPECTRALE DES CHAÎNES DE SOPHIE GERMAIN MOD 30")
print("  Projet Couret-Unification — Mars 2026")
print("=" * 70)

# ============================================================================
# PHASE 1 : Identification des nombres de Sophie Germain
# ============================================================================
print("\n📌 PHASE 1 : Identification des nombres de Sophie Germain")
print("-" * 50)

t0 = time.time()

sophie_germain_primes = []
safe_primes = []

for p in primerange(2, LIMIT):
    q = 2 * p + 1
    if isprime(q):
        sophie_germain_primes.append(p)
        safe_primes.append(q)

t1 = time.time()
print(f"  Nombres de Sophie Germain trouvés : {len(sophie_germain_primes)}")
print(f"  Limite : {LIMIT:,}")
print(f"  Temps : {t1 - t0:.2f}s")
print(f"  Premiers SG : {sophie_germain_primes[:15]}...")
print(f"  Derniers SG  : {sophie_germain_primes[-5:]}")

# ============================================================================
# PHASE 2 : Construction des chaînes de Cunningham (1ère espèce)
# ============================================================================
print("\n📌 PHASE 2 : Construction des chaînes de Cunningham")
print("-" * 50)

sg_set = set(sophie_germain_primes)
all_primes_set = set(primerange(2, 4 * LIMIT))  # Marge pour les safe primes

def build_cunningham_chain(start):
    """Construit la chaîne de Cunningham de 1ère espèce partant de start."""
    chain = [start]
    current = start
    while True:
        next_val = 2 * current + 1
        if next_val in all_primes_set:
            chain.append(next_val)
            current = next_val
        else:
            break
    return chain

# Trouver les débuts de chaînes (SG primes qui ne sont pas eux-mêmes des safe primes d'un SG antérieur)
chain_starts = []
for p in sophie_germain_primes:
    # p est début de chaîne si (p-1)/2 n'est pas premier ou n'est pas SG
    predecessor = (p - 1) // 2
    if p % 2 == 0:
        continue
    if predecessor < 2 or not isprime(predecessor) or predecessor not in sg_set:
        chain_starts.append(p)

chains = []
chain_lengths = defaultdict(int)

for start in chain_starts:
    chain = build_cunningham_chain(start)
    if len(chain) >= 2:  # Au moins une transition
        chains.append(chain)
    chain_lengths[len(chain)] += 1

print(f"  Débuts de chaînes identifiés : {len(chain_starts)}")
print(f"  Chaînes avec ≥ 2 éléments : {len(chains)}")
print(f"\n  Distribution des longueurs de chaînes :")
for length in sorted(chain_lengths.keys()):
    print(f"    Longueur {length} : {chain_lengths[length]} chaînes")

# Exemples de chaînes longues
long_chains = sorted(chains, key=len, reverse=True)[:10]
print(f"\n  Top 10 chaînes les plus longues :")
for i, chain in enumerate(long_chains):
    residues_chain = [c % 30 for c in chain]
    suites = [f"S.{r}" for r in residues_chain]
    print(f"    #{i+1} (longueur {len(chain)}) : {chain} → {' → '.join(suites)}")

# ============================================================================
# PHASE 3 : Matrice de transition mod 30
# ============================================================================
print("\n📌 PHASE 3 : Matrice de transition Sophie Germain mod 30")
print("-" * 50)

# Méthode 1 : Transitions dans les CHAÎNES de Cunningham
transition_counts_chains = np.zeros((8, 8), dtype=int)

for chain in chains:
    for k in range(len(chain) - 1):
        r_current = chain[k] % 30
        r_next = chain[k + 1] % 30
        if r_current in RES_TO_IDX and r_next in RES_TO_IDX:
            i = RES_TO_IDX[r_current]
            j = RES_TO_IDX[r_next]
            transition_counts_chains[i, j] += 1

print("  Matrice de comptage (transitions dans les chaînes) :")
print(f"  {'':>5}", end="")
for r in RESIDUES:
    print(f"  S.{r:>2}", end="")
print()
for i, r in enumerate(RESIDUES):
    print(f"  S.{r:>2}", end="")
    for j in range(8):
        print(f"  {transition_counts_chains[i,j]:>4}", end="")
    print(f"  | Σ={transition_counts_chains[i,:].sum()}")

total_transitions_chains = transition_counts_chains.sum()
print(f"\n  Total transitions (chaînes) : {total_transitions_chains}")

# Méthode 2 : Transitions DIRECTES p → 2p+1 pour tous les SG
transition_counts_direct = np.zeros((8, 8), dtype=int)

for p in sophie_germain_primes:
    q = 2 * p + 1
    r_p = p % 30
    r_q = q % 30
    if r_p in RES_TO_IDX and r_q in RES_TO_IDX:
        i = RES_TO_IDX[r_p]
        j = RES_TO_IDX[r_q]
        transition_counts_direct[i, j] += 1

print("\n  Matrice de comptage (transitions directes p → 2p+1) :")
print(f"  {'':>5}", end="")
for r in RESIDUES:
    print(f"  S.{r:>2}", end="")
print()
for i, r in enumerate(RESIDUES):
    print(f"  S.{r:>2}", end="")
    for j in range(8):
        print(f"  {transition_counts_direct[i,j]:>4}", end="")
    print(f"  | Σ={transition_counts_direct[i,:].sum()}")

total_transitions_direct = transition_counts_direct.sum()
print(f"\n  Total transitions (directes) : {total_transitions_direct}")

# ============================================================================
# PHASE 4 : Normalisation et analyse spectrale
# ============================================================================
print("\n📌 PHASE 4 : Analyse spectrale")
print("-" * 50)

# Normalisation en matrice stochastique (lignes somment à 1)
M_direct = np.zeros((8, 8))
for i in range(8):
    row_sum = transition_counts_direct[i, :].sum()
    if row_sum > 0:
        M_direct[i, :] = transition_counts_direct[i, :] / row_sum
    else:
        M_direct[i, :] = 1.0 / 8  # Régularisation uniforme

print("  Matrice de transition normalisée M (directe) :")
print(f"  {'':>5}", end="")
for r in RESIDUES:
    print(f"   S.{r:>2}", end="")
print()
for i, r in enumerate(RESIDUES):
    print(f"  S.{r:>2}", end="")
    for j in range(8):
        print(f"  {M_direct[i,j]:.4f}", end="")
    print()

# Vérification stochastique
row_sums = M_direct.sum(axis=1)
print(f"\n  Sommes des lignes : {row_sums}")
print(f"  Matrice stochastique : {'✓ OUI' if np.allclose(row_sums, 1.0) else '✗ NON'}")

# Valeurs propres
eigenvalues_direct = np.linalg.eigvals(M_direct)
eigenvalues_sorted = sorted(eigenvalues_direct, key=lambda x: -abs(x))

print(f"\n  ⚡ VALEURS PROPRES de M (directe) :")
print(f"  {'#':>3}  {'Valeur propre':>20}  {'|λ|':>10}  {'Écart à 1/√7':>15}")
print(f"  {'─'*3}  {'─'*20}  {'─'*10}  {'─'*15}")
for k, ev in enumerate(eigenvalues_sorted):
    mod = abs(ev)
    ecart = abs(mod - LAMBDA_TARGET)
    marker = " ◄◄◄ PROCHE DE 1/√7 !" if ecart < 0.05 else ""
    if np.isreal(ev):
        print(f"  {k+1:>3}  {ev.real:>20.8f}  {mod:>10.8f}  {ecart:>15.8f}{marker}")
    else:
        print(f"  {k+1:>3}  {ev:>20}  {mod:>10.8f}  {ecart:>15.8f}{marker}")

print(f"\n  λ cible (1/√7) = {LAMBDA_TARGET:.8f}")

# Distribution stationnaire
eigenvalues_real, eigenvectors = np.linalg.eig(M_direct.T)
idx_one = np.argmin(np.abs(eigenvalues_real - 1.0))
stationary = np.real(eigenvectors[:, idx_one])
stationary = stationary / stationary.sum()

print(f"\n  📊 Distribution stationnaire π :")
for i, r in enumerate(RESIDUES):
    print(f"    S.{r:>2} : {stationary[i]:.6f}  (théorique uniforme : {1/8:.6f})")

deviation = np.max(np.abs(stationary - 1/8))
print(f"\n  Déviation max par rapport à l'uniformité : {deviation:.6f}")

# ============================================================================
# PHASE 5 : Analyse détaillée de la structure de transition
# ============================================================================
print("\n📌 PHASE 5 : Analyse algébrique de la transition p → 2p+1 mod 30")
print("-" * 50)

print("  Fonction de transition théorique f(r) = (2r + 1) mod 30 :")
print(f"  {'r':>5} → {'f(r)':>5}  {'Suite départ':>15} → {'Suite arrivée':>15}")
for r in RESIDUES:
    f_r = (2 * r + 1) % 30
    suite_arr = f"S.{f_r}" if f_r in RESIDUES else f"{f_r} (hors suites !)"
    print(f"  {r:>5} → {f_r:>5}  S.{r:>2}{'':>11} → {suite_arr}")

# Transitions théoriques DÉTERMINISTES
print("\n  ⚠️  OBSERVATION FONDAMENTALE :")
print("  La transition p → 2p+1 est DÉTERMINISTE modulo 30 !")
print("  f(r) = (2r + 1) mod 30 est une FONCTION, pas une relation aléatoire.")
print()

theoretical_map = {}
for r in RESIDUES:
    f_r = (2 * r + 1) % 30
    theoretical_map[r] = f_r
    in_residues = f_r in RESIDUES
    print(f"    S.{r:>2} → {f_r:>2} {'(dans R₃₀ ✓)' if in_residues else '(HORS R₃₀ ✗)'}")

# Identifier les classes source possibles
print("\n  Classes qui RESTENT dans R₃₀ après transformation :")
valid_sources = []
for r in RESIDUES:
    f_r = (2 * r + 1) % 30
    if f_r in RESIDUES:
        valid_sources.append((r, f_r))
        print(f"    S.{r} → S.{f_r} ✓")

print(f"\n  Nombre de transitions valides : {len(valid_sources)} / 8")
print(f"  Transitions impossibles (sortent de R₃₀) :")
for r in RESIDUES:
    f_r = (2 * r + 1) % 30
    if f_r not in RESIDUES:
        print(f"    S.{r} → {f_r} ✗ (non copremier à 30)")

# ============================================================================
# PHASE 6 : Analyse par suites sources
# ============================================================================
print("\n📌 PHASE 6 : Statistiques par suite source")
print("-" * 50)

sg_by_residue = defaultdict(list)
for p in sophie_germain_primes:
    r = p % 30
    sg_by_residue[r].append(p)

print(f"  {'Suite':>8}  {'Count':>8}  {'% du total':>10}  {'Exemples':>40}")
for r in RESIDUES:
    count = len(sg_by_residue[r])
    pct = 100 * count / len(sophie_germain_primes) if sophie_germain_primes else 0
    examples = sg_by_residue[r][:5]
    print(f"  S.{r:>2}     {count:>8}  {pct:>9.2f}%  {examples}")

# Biais de Tchebychev
print(f"\n  Analyse du biais de Tchebychev :")
mean_count = len(sophie_germain_primes) / 8
for r in RESIDUES:
    count = len(sg_by_residue[r])
    bias = (count - mean_count) / mean_count * 100
    bar = "+" * int(abs(bias) * 2) if bias > 0 else "-" * int(abs(bias) * 2)
    print(f"    S.{r:>2} : {count:>6}  (biais = {bias:>+7.2f}%)  {'▓' if bias > 0 else '░'}{bar}")

# ============================================================================
# PHASE 7 : Matrice de transition ÉLARGIE (consécutifs SG)
# ============================================================================
print("\n📌 PHASE 7 : Matrice de transition entre SG consécutifs")
print("-" * 50)

transition_consecutive = np.zeros((8, 8), dtype=int)
for k in range(len(sophie_germain_primes) - 1):
    p1 = sophie_germain_primes[k]
    p2 = sophie_germain_primes[k + 1]
    r1 = p1 % 30
    r2 = p2 % 30
    if r1 in RES_TO_IDX and r2 in RES_TO_IDX:
        i = RES_TO_IDX[r1]
        j = RES_TO_IDX[r2]
        transition_consecutive[i, j] += 1

M_consecutive = np.zeros((8, 8))
for i in range(8):
    row_sum = transition_consecutive[i, :].sum()
    if row_sum > 0:
        M_consecutive[i, :] = transition_consecutive[i, :] / row_sum

print("  Matrice de transition (SG consécutifs) :")
print(f"  {'':>5}", end="")
for r in RESIDUES:
    print(f"   S.{r:>2}", end="")
print()
for i, r in enumerate(RESIDUES):
    print(f"  S.{r:>2}", end="")
    for j in range(8):
        print(f"  {M_consecutive[i,j]:.4f}", end="")
    print()

eigenvalues_consec = np.linalg.eigvals(M_consecutive)
eigenvalues_consec_sorted = sorted(eigenvalues_consec, key=lambda x: -abs(x))

print(f"\n  ⚡ VALEURS PROPRES de M (SG consécutifs) :")
print(f"  {'#':>3}  {'|λ|':>12}  {'Re(λ)':>12}  {'Im(λ)':>12}  {'Écart à 1/√7':>15}")
for k, ev in enumerate(eigenvalues_consec_sorted):
    mod = abs(ev)
    ecart = abs(mod - LAMBDA_TARGET)
    marker = " ◄◄◄" if ecart < 0.05 else ""
    print(f"  {k+1:>3}  {mod:>12.8f}  {ev.real:>12.8f}  {ev.imag:>12.8f}  {ecart:>15.8f}{marker}")

# Comparaison avec Lemke Oliver & Soundararajan (biais consécutifs)
print(f"\n  📊 Comparaison avec biais Lemke Oliver-Soundararajan :")
print(f"  La matrice M_consecutive capture le biais de transition entre SG consécutifs.")
print(f"  Si M était uniforme, chaque entrée serait {1/8:.4f}.")

max_entry = M_consecutive.max()
min_entry = M_consecutive[M_consecutive > 0].min() if (M_consecutive > 0).any() else 0
print(f"  Entrée max : {max_entry:.4f}")
print(f"  Entrée min (>0) : {min_entry:.4f}")
print(f"  Ratio max/min : {max_entry/min_entry:.4f}" if min_entry > 0 else "  Ratio : N/A")

# ============================================================================
# PHASE 8 : Synthèse et test λ = 1/√7
# ============================================================================
print("\n" + "=" * 70)
print("  📊 SYNTHÈSE FINALE")
print("=" * 70)

print(f"\n  🎯 Constante cible : λ = 1/√7 = {LAMBDA_TARGET:.8f}")
print()

# Test sur toutes les matrices
matrices = {
    "M_direct (p → 2p+1)": eigenvalues_sorted,
    "M_consecutive (SG consécutifs)": eigenvalues_consec_sorted,
}

for name, evs in matrices.items():
    print(f"  📈 {name} :")
    closest = min(evs, key=lambda x: abs(abs(x) - LAMBDA_TARGET))
    ecart = abs(abs(closest) - LAMBDA_TARGET)
    print(f"    Valeur propre la plus proche de 1/√7 : |λ| = {abs(closest):.8f}")
    print(f"    Écart : {ecart:.8f} ({ecart/LAMBDA_TARGET*100:.2f}%)")
    print()

# ============================================================================
# PHASE 9 : Visualisations
# ============================================================================
print("\n📌 PHASE 9 : Génération des visualisations")
print("-" * 50)

fig, axes = plt.subplots(2, 3, figsize=(18, 12))
fig.suptitle("Analyse Spectrale des Chaînes de Sophie Germain mod 30\nProjet Couret-Unification",
             fontsize=14, fontweight='bold')

# 1. Distribution des SG par suite
ax = axes[0, 0]
counts = [len(sg_by_residue[r]) for r in RESIDUES]
colors = ['#e74c3c' if c > mean_count else '#3498db' for c in counts]
bars = ax.bar([f"S.{r}" for r in RESIDUES], counts, color=colors, edgecolor='black', linewidth=0.5)
ax.axhline(y=mean_count, color='green', linestyle='--', linewidth=1.5, label=f'Moyenne = {mean_count:.0f}')
ax.set_title("Distribution des SG par suite mod 30")
ax.set_ylabel("Nombre de Sophie Germain")
ax.legend()
ax.grid(axis='y', alpha=0.3)

# 2. Heatmap matrice de transition directe
ax = axes[0, 1]
im = ax.imshow(M_direct, cmap='YlOrRd', aspect='equal')
ax.set_xticks(range(8))
ax.set_xticklabels([f"S.{r}" for r in RESIDUES], fontsize=8)
ax.set_yticks(range(8))
ax.set_yticklabels([f"S.{r}" for r in RESIDUES], fontsize=8)
ax.set_title("Matrice de transition\np → 2p+1 (directe)")
for i in range(8):
    for j in range(8):
        val = M_direct[i, j]
        if val > 0:
            ax.text(j, i, f'{val:.3f}', ha='center', va='center', fontsize=7,
                   color='white' if val > 0.5 else 'black')
plt.colorbar(im, ax=ax, shrink=0.8)

# 3. Heatmap matrice de transition consécutive
ax = axes[0, 2]
im2 = ax.imshow(M_consecutive, cmap='YlOrRd', aspect='equal')
ax.set_xticks(range(8))
ax.set_xticklabels([f"S.{r}" for r in RESIDUES], fontsize=8)
ax.set_yticks(range(8))
ax.set_yticklabels([f"S.{r}" for r in RESIDUES], fontsize=8)
ax.set_title("Matrice de transition\nSG consécutifs")
for i in range(8):
    for j in range(8):
        val = M_consecutive[i, j]
        if val > 0:
            ax.text(j, i, f'{val:.3f}', ha='center', va='center', fontsize=7,
                   color='white' if val > 0.5 else 'black')
plt.colorbar(im2, ax=ax, shrink=0.8)

# 4. Spectre de M_direct (valeurs propres dans le plan complexe)
ax = axes[1, 0]
evs_direct = eigenvalues_sorted
ax.scatter([ev.real for ev in evs_direct], [ev.imag for ev in evs_direct],
           s=100, c='red', zorder=5, edgecolors='black', linewidths=1)
theta = np.linspace(0, 2*np.pi, 100)
ax.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.3, label='|λ|=1')
ax.plot(LAMBDA_TARGET * np.cos(theta), LAMBDA_TARGET * np.sin(theta),
        'g--', alpha=0.5, label=f'|λ|=1/√7≈{LAMBDA_TARGET:.4f}')
ax.axhline(y=0, color='gray', linewidth=0.5)
ax.axvline(x=0, color='gray', linewidth=0.5)
ax.set_title("Spectre de M (directe)")
ax.set_xlabel("Re(λ)")
ax.set_ylabel("Im(λ)")
ax.legend(fontsize=8)
ax.set_aspect('equal')
ax.grid(alpha=0.3)

# 5. Spectre de M_consecutive
ax = axes[1, 1]
evs_consec = eigenvalues_consec_sorted
ax.scatter([ev.real for ev in evs_consec], [ev.imag for ev in evs_consec],
           s=100, c='blue', zorder=5, edgecolors='black', linewidths=1)
ax.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.3, label='|λ|=1')
ax.plot(LAMBDA_TARGET * np.cos(theta), LAMBDA_TARGET * np.sin(theta),
        'g--', alpha=0.5, label=f'|λ|=1/√7≈{LAMBDA_TARGET:.4f}')
ax.axhline(y=0, color='gray', linewidth=0.5)
ax.axvline(x=0, color='gray', linewidth=0.5)
ax.set_title("Spectre de M (SG consécutifs)")
ax.set_xlabel("Re(λ)")
ax.set_ylabel("Im(λ)")
ax.legend(fontsize=8)
ax.set_aspect('equal')
ax.grid(alpha=0.3)

# 6. Distribution des longueurs de chaînes
ax = axes[1, 2]
lengths = sorted(chain_lengths.keys())
counts_lengths = [chain_lengths[l] for l in lengths]
ax.bar([str(l) for l in lengths], counts_lengths, color='#9b59b6', edgecolor='black', linewidth=0.5)
ax.set_title("Distribution des longueurs\nde chaînes de Cunningham")
ax.set_xlabel("Longueur de chaîne")
ax.set_ylabel("Nombre de chaînes")
ax.grid(axis='y', alpha=0.3)
for i, (l, c) in enumerate(zip(lengths, counts_lengths)):
    ax.text(i, c + max(counts_lengths)*0.02, str(c), ha='center', va='bottom', fontsize=9)

plt.tight_layout()
plt.savefig('docs/towerlift/sophie_germain_spectral.png', dpi=150, bbox_inches='tight')
print("  ✓ Figure principale sauvegardée")

# ============================================================================
# FIGURE 2 : Graphe des transitions
# ============================================================================
fig2, ax2 = plt.subplots(1, 1, figsize=(10, 10))
ax2.set_title("Graphe des transitions Sophie Germain mod 30\n(épaisseur ∝ fréquence)", fontsize=13)

# Positions sur un cercle
angles = np.linspace(0, 2*np.pi, 8, endpoint=False) - np.pi/2
positions = {RESIDUES[i]: (np.cos(angles[i]), np.sin(angles[i])) for i in range(8)}

# Dessiner les arêtes
max_weight = M_consecutive.max()
for i in range(8):
    for j in range(8):
        w = M_consecutive[i, j]
        if w > 0.01:
            x1, y1 = positions[RESIDUES[i]]
            x2, y2 = positions[RESIDUES[j]]
            if i == j:
                # Self-loop
                circle = plt.Circle((x1*1.15, y1*1.15), 0.08, fill=False,
                                   linewidth=w/max_weight*5, color='red', alpha=0.6)
                ax2.add_patch(circle)
            else:
                dx, dy = x2 - x1, y2 - y1
                ax2.annotate("", xy=(x2*0.88, y2*0.88), xytext=(x1*0.88, y1*0.88),
                            arrowprops=dict(arrowstyle="->", lw=w/max_weight*5,
                                          color=plt.cm.viridis(w/max_weight), alpha=0.7,
                                          connectionstyle="arc3,rad=0.1"))

# Dessiner les nœuds
for r in RESIDUES:
    x, y = positions[r]
    count = len(sg_by_residue[r])
    size = 800 + count * 0.3
    color = '#e74c3c' if count > mean_count else '#3498db'
    ax2.scatter(x, y, s=size, c=color, edgecolors='black', linewidths=2, zorder=10)
    ax2.text(x, y, f"S.{r}\n({count})", ha='center', va='center', fontsize=9, fontweight='bold', zorder=11)

ax2.set_xlim(-1.5, 1.5)
ax2.set_ylim(-1.5, 1.5)
ax2.set_aspect('equal')
ax2.axis('off')

plt.tight_layout()
plt.savefig('docs/towerlift/sophie_germain_graph.png', dpi=150, bbox_inches='tight')
print("  ✓ Graphe des transitions sauvegardé")

# ============================================================================
# Export JSON pour réutilisation
# ============================================================================
timestamp = datetime.now().strftime("%Y-%m-%d")
results = {
    "metadata": {
        "date": timestamp,
        "limit": LIMIT,
        "total_sg": len(sophie_germain_primes),
        "total_chains": len(chains),
        "lambda_target": LAMBDA_TARGET,
    },
    "distribution_mod30": {f"S.{r}": len(sg_by_residue[r]) for r in RESIDUES},
    "chain_length_distribution": {str(k): v for k, v in sorted(chain_lengths.items())},
    "eigenvalues_direct": [{"real": ev.real, "imag": ev.imag, "modulus": abs(ev)} for ev in eigenvalues_sorted],
    "eigenvalues_consecutive": [{"real": ev.real, "imag": ev.imag, "modulus": abs(ev)} for ev in eigenvalues_consec_sorted],
    "stationary_distribution": {f"S.{r}": float(stationary[i]) for i, r in enumerate(RESIDUES)},
    "transition_matrix_direct": M_direct.tolist(),
    "transition_matrix_consecutive": M_consecutive.tolist(),
}

with open('docs/towerlift/sophie_germain_results.json', 'w') as f:
    json.dump(results, f, indent=2)
print("  ✓ Résultats JSON exportés")

print("\n" + "=" * 70)
print("  ✅ ANALYSE COMPLÈTE TERMINÉE")
print("=" * 70)
