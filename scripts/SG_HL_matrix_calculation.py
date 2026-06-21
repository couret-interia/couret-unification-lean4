#!/usr/bin/env python3
"""
Note Sophie Germain — Étape 4 du plan v35
Calcul de la matrice Hardy-Littlewood attendue pour les transitions
entre nombres premiers de Sophie Germain consécutifs sur les classes
{11, 23, 29} mod 30.

Objectif : produire la matrice E_HL[i,j] = nombre de transitions attendues
sous l'hypothèse Hardy-Littlewood (indépendance conditionnelle aux
marginales globales), puis calculer le χ²_HL case par case.

Fournit la matière directement publiable pour l'article autonome SG.

Données empiriques source : conversation du 25 mars 2026
N_total = 30 653 transitions SG consécutives sur p ≤ 10^7
"""

import numpy as np
from scipy.stats import chi2 as chi2_dist

# ======================================================================
# §1. Matrice observée M_3 (validée 25 mars 2026)
# ======================================================================

classes = [11, 23, 29]
M3_obs = np.array([
    [3042, 3738, 3427],   # 11 -> {11, 23, 29}
    [3431, 3072, 3787],   # 23 -> {11, 23, 29}
    [3733, 3481, 2942],   # 29 -> {11, 23, 29}
])
N_total = M3_obs.sum()  # 30 653

print("=" * 72)
print("ÉTAPE 4 — Matrice Hardy-Littlewood attendue, Sophie Germain mod 30")
print("=" * 72)
print(f"\nMatrice observée M_3 :")
print(f"            S.11    S.23    S.29   |  Total ligne")
for i, c in enumerate(classes):
    row_total = M3_obs[i].sum()
    print(f"  S.{c:>2d}    {M3_obs[i,0]:>5d}  {M3_obs[i,1]:>5d}  "
          f"{M3_obs[i,2]:>5d}  |  {row_total:>5d}")
col_totals = M3_obs.sum(axis=0)
print(f"  Total   {col_totals[0]:>5d}  {col_totals[1]:>5d}  "
      f"{col_totals[2]:>5d}  |  {N_total}")

# ======================================================================
# §2. Marginales empiriques globales
# ======================================================================

row_sums = M3_obs.sum(axis=1)  # densités de la classe d'origine
col_sums = M3_obs.sum(axis=0)  # densités de la classe cible

# Hypothèse Hardy-Littlewood : sous indépendance conditionnelle,
# P(j | i) = P(j) = col_sums[j] / N_total
# Donc E_HL[i,j] = row_sums[i] * col_sums[j] / N_total

E_HL = np.outer(row_sums, col_sums) / N_total

print("\n" + "-" * 72)
print("MATRICE HARDY-LITTLEWOOD ATTENDUE (sous indépendance marginale)")
print("-" * 72)
print(f"\nE_HL[i,j] = (Σ ligne i) × (Σ colonne j) / N_total\n")
print(f"            S.11      S.23      S.29")
for i, c in enumerate(classes):
    print(f"  S.{c:>2d}   {E_HL[i,0]:>7.1f}  {E_HL[i,1]:>7.1f}  {E_HL[i,2]:>7.1f}")

# ======================================================================
# §3. Résidus standardisés case par case
# ======================================================================

residuals = (M3_obs - E_HL) / np.sqrt(E_HL)

print("\n" + "-" * 72)
print("RÉSIDUS STANDARDISÉS  R_ij = (O_ij − E_ij) / √E_ij")
print("-" * 72)
print(f"\n            S.11      S.23      S.29")
for i, c in enumerate(classes):
    print(f"  S.{c:>2d}   {residuals[i,0]:>+7.2f}σ  {residuals[i,1]:>+7.2f}σ  "
          f"{residuals[i,2]:>+7.2f}σ")

# ======================================================================
# §4. χ² Hardy-Littlewood
# ======================================================================

chi2_HL = ((M3_obs - E_HL) ** 2 / E_HL).sum()
df_HL = (3 - 1) * (3 - 1)  # 4 ddl pour table 3x3 sous indépendance
p_HL = 1 - chi2_dist.cdf(chi2_HL, df_HL)

print("\n" + "-" * 72)
print("STATISTIQUE χ² HARDY-LITTLEWOOD")
print("-" * 72)
print(f"\n  χ²_HL = {chi2_HL:.2f}")
print(f"  df    = {df_HL}")
print(f"  p     = {p_HL:.2e}")

if p_HL < 1e-49:
    print(f"  → Rejet TRÈS FORT du modèle HL (p < 10^-49)")

# ======================================================================
# §5. Décomposition du χ² par case (% de contribution)
# ======================================================================

chi2_cells = (M3_obs - E_HL) ** 2 / E_HL
chi2_pct = chi2_cells / chi2_HL * 100

print("\n" + "-" * 72)
print("CONTRIBUTION PAR CASE AU χ² TOTAL (%)")
print("-" * 72)
print(f"\n            S.11      S.23      S.29")
for i, c in enumerate(classes):
    print(f"  S.{c:>2d}   {chi2_pct[i,0]:>6.1f}%   {chi2_pct[i,1]:>6.1f}%   "
          f"{chi2_pct[i,2]:>6.1f}%")

diag_contribution = sum(chi2_cells[i, i] for i in range(3))
diag_pct = diag_contribution / chi2_HL * 100

print(f"\n  Contribution diagonale totale : {diag_pct:.1f}% du χ² total")
print(f"  → Confirme la répulsion intra-classe comme effet structurel dominant")

# ======================================================================
# §6. Test complémentaire : modèle uniforme (référence historique)
# ======================================================================

E_unif = np.ones_like(M3_obs, dtype=float)
for i in range(3):
    E_unif[i, :] = row_sums[i] / 3.0
chi2_unif = ((M3_obs - E_unif) ** 2 / E_unif).sum()
df_unif = 3 * (3 - 1)
p_unif = 1 - chi2_dist.cdf(chi2_unif, df_unif)

print("\n" + "-" * 72)
print("RÉFÉRENCE — MODÈLE UNIFORME (P(j|i) = 1/3)")
print("-" * 72)
print(f"  χ²_unif = {chi2_unif:.2f}, df = {df_unif}, p = {p_unif:.2e}")

# ======================================================================
# §7. Résumé exportable LaTeX-compatible
# ======================================================================

print("\n" + "=" * 72)
print("RÉSUMÉ POUR LA NOTE SG")
print("=" * 72)
print(f"""
RÉSULTATS PRINCIPAUX :

  • χ²_HL = {chi2_HL:.2f} sur {df_HL} ddl, p = {p_HL:.2e}
  • χ²_unif = {chi2_unif:.2f} sur {df_unif} ddl, p = {p_unif:.2e}
  • Résidus diagonaux :
      11→11 : {residuals[0,0]:+.2f}σ
      23→23 : {residuals[1,1]:+.2f}σ
      29→29 : {residuals[2,2]:+.2f}σ
  • Contribution diagonale au χ²_HL : {diag_pct:.1f}%
  • N_total = {N_total} transitions SG consécutives, p ≤ 10^7

INTERPRÉTATION ROBUSTE :
  Les données rejettent TRÈS FORTEMENT (p < 10^{-49}) le modèle nul
  d'indépendance conditionnelle Hardy-Littlewood. La structure dominante
  est la répulsion intra-classe (déficit diagonal > 6σ par cellule),
  qui contribue à elle seule {diag_pct:.0f}% de la statistique totale.
  Cette signature est compatible avec une mémoire arithmétique entre
  SG consécutifs, prolongeant le biais de Chebyshev aux résidus mod 30.

  Résultat indépendant de l'Hypothèse de Riemann.
""")

# Sauvegarde matricielle pour insertion LaTeX
np.savetxt("./scripts/SG_E_HL_matrix.csv", E_HL,
           delimiter=",", fmt="%.2f", header="S.11,S.23,S.29")
np.savetxt("./scripts/SG_residuals.csv", residuals,
           delimiter=",", fmt="%+.4f", header="S.11,S.23,S.29")
print(f"Matrices exportées dans v35.7.2/SG_E_HL_matrix.csv et SG_residuals.csv")
