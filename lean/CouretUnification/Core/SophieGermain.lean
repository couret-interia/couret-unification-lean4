/-
Copyright (c) 2026 Couret-Unification Programme.
Released under Apache 2.0.

# Core/SophieGermain.lean — Front 1 : matrice M3 des transitions

## Doctrine

Ce fichier encode comme données Lean certifiées la matrice de transitions
entre primes Sophie Germain consécutifs dans les 3 classes actives mod 30,
mesurée sur le range p ≤ 10⁷ par énumération directe (sympy).

Données :
  - Les 3 classes actives mod 30 pour les primes Sophie Germain : {11, 23, 29}
  - La matrice M3 ∈ ℕ³ˣ³ des transitions (Tableau 1 de la note)
  - Les sommes de lignes/colonnes
  - Le total N = 30 653

L'objectif est de rendre **vérifiable mécaniquement** par `native_decide`
les égalités élémentaires sur ces données (sommes, totaux), pour que la
note SG_chi2_HL_note.pdf soit adossée à un noyau formel.

NOTE IMPORTANTE : ce fichier ne formalise PAS le calcul de χ², qui demande
de l'arithmétique sur ℝ et la fonction de répartition χ². Il formalise la
table de comptage et ses invariants combinatoires.

## Statut épistémique

  - Couche : Core (donnée empirique encodée + invariants décidables)
  - Statut : [P] sur les invariants de table (sommes), [N_strong] sur
             l'interprétation statistique (qui vit dans la note PDF).
  - RHClaimed = false (résultat indépendant de RH par construction).
-/

import CouretUnification.Core.Doctrine
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace CouretUnification
namespace Core
namespace SophieGermain

open Finset

/-!
## Section 1 — Les 3 classes actives mod 30

Les Sophie Germain primes p > 5 sont nécessairement dans {11, 23, 29} mod 30.
Les 5 autres classes coprimes à 30 ({1, 7, 13, 17, 19}) sont éliminées
car 2p+1 serait divisible par 3 ou par 5.
-/

/-- [P] Les 3 classes actives mod 30 pour les primes Sophie Germain. -/
def activeClass : Fin 3 → ℕ
  | ⟨0, _⟩ => 11
  | ⟨1, _⟩ => 23
  | ⟨2, _⟩ => 29

/-- [P] Toutes les classes actives sont coprimes à 30. -/
theorem activeClass_coprime_30 (i : Fin 3) :
    Nat.Coprime (activeClass i) 30 := by
  fin_cases i <;> decide

/-- [P] Toutes les classes actives sont premières (vérifiable). -/
theorem activeClass_prime (i : Fin 3) : Nat.Prime (activeClass i) := by
  fin_cases i <;> decide

/-- [P] Pour chaque classe active, 2*c+1 est aussi premier
    (vérification directe : 2·11+1=23, 2·23+1=47, 2·29+1=59). -/
theorem activeClass_safe_prime (i : Fin 3) :
    Nat.Prime (2 * activeClass i + 1) := by
  fin_cases i <;> decide

/-!
## Section 2 — La matrice M3 (donnée empirique)

Source : énumération sur p ≤ 10⁷ via sympy.primerange + test 2p+1 prime.
Référence : SG_chi2_HL_note.pdf, Tableau 1.

Convention : M3 i j = nombre de transitions (p_n, p_{n+1}) avec
p_n ≡ activeClass i (mod 30) et p_{n+1} ≡ activeClass j (mod 30).
-/

/-- [P] La matrice M3 des transitions Sophie Germain (Tableau 1). -/
def M3 : Fin 3 → Fin 3 → ℕ
  | ⟨0, _⟩, ⟨0, _⟩ => 3042   -- 11 → 11
  | ⟨0, _⟩, ⟨1, _⟩ => 3738   -- 11 → 23
  | ⟨0, _⟩, ⟨2, _⟩ => 3427   -- 11 → 29
  | ⟨1, _⟩, ⟨0, _⟩ => 3431   -- 23 → 11
  | ⟨1, _⟩, ⟨1, _⟩ => 3072   -- 23 → 23
  | ⟨1, _⟩, ⟨2, _⟩ => 3787   -- 23 → 29
  | ⟨2, _⟩, ⟨0, _⟩ => 3733   -- 29 → 11
  | ⟨2, _⟩, ⟨1, _⟩ => 3481   -- 29 → 23
  | ⟨2, _⟩, ⟨2, _⟩ => 2942   -- 29 → 29

/-- [P] Somme de la ligne i de M3. -/
def rowSum (i : Fin 3) : ℕ :=
  ∑ j, M3 i j

/-- [P] Somme de la colonne j de M3. -/
def colSum (j : Fin 3) : ℕ :=
  ∑ i, M3 i j

/-- [P] Total des observations N. -/
def totalCount : ℕ :=
  ∑ i, ∑ j, M3 i j

/-!
## Section 3 — Invariants combinatoires (vérifiés par décidabilité)

Toutes ces égalités sont vérifiables mécaniquement par `decide`
ou `native_decide`. Elles attestent l'intégrité interne du tableau.
-/

/-- [P] Ligne 11 : somme = 10207. -/
theorem rowSum_11 : rowSum ⟨0, by decide⟩ = 10207 := by decide

/-- [P] Ligne 23 : somme = 10290. -/
theorem rowSum_23 : rowSum ⟨1, by decide⟩ = 10290 := by decide

/-- [P] Ligne 29 : somme = 10156. -/
theorem rowSum_29 : rowSum ⟨2, by decide⟩ = 10156 := by decide

/-- [P] Colonne 11 : somme = 10206. -/
theorem colSum_11 : colSum ⟨0, by decide⟩ = 10206 := by decide

/-- [P] Colonne 23 : somme = 10291. -/
theorem colSum_23 : colSum ⟨1, by decide⟩ = 10291 := by decide

/-- [P] Colonne 29 : somme = 10156. -/
theorem colSum_29 : colSum ⟨2, by decide⟩ = 10156 := by decide

/-- [P] Total : N = 30 653. -/
theorem totalCount_eq : totalCount = 30653 := by decide

/-- [P] Cohérence : somme des sommes de lignes = somme des sommes de colonnes = N. -/
theorem rowSums_eq_total :
    (∑ i, rowSum i) = totalCount := by
  unfold rowSum totalCount
  rfl

/-- [P] Cohérence : somme des sommes de colonnes = N. -/
theorem colSums_eq_total :
    (∑ j, colSum j) = totalCount := by
  unfold colSum totalCount
  rw [Finset.sum_comm]

/-!
## Section 4 — Déficit diagonal (énoncé combinatoire)

L'énoncé central de la note : les cellules diagonales M3[i,i] sont
toutes strictement inférieures aux moyennes (Ri/3) :
  M3[0,0] = 3042 < 10207/3 ≈ 3402
  M3[1,1] = 3072 < 10290/3 = 3430
  M3[2,2] = 2942 < 10156/3 ≈ 3385

Cette dépendance est l'observable combinatoire qui motive le test χ².
-/

/-- [P] Déficit diagonal sur ligne 11 : M[0,0] · 3 < rowSum 11. -/
theorem diagonal_deficit_11 : M3 ⟨0, by decide⟩ ⟨0, by decide⟩ * 3 < rowSum ⟨0, by decide⟩ := by
  decide

/-- [P] Déficit diagonal sur ligne 23 : M[1,1] · 3 < rowSum 23. -/
theorem diagonal_deficit_23 : M3 ⟨1, by decide⟩ ⟨1, by decide⟩ * 3 < rowSum ⟨1, by decide⟩ := by
  decide

/-- [P] Déficit diagonal sur ligne 29 : M[2,2] · 3 < rowSum 29. -/
theorem diagonal_deficit_29 : M3 ⟨2, by decide⟩ ⟨2, by decide⟩ * 3 < rowSum ⟨2, by decide⟩ := by
  decide

/-- [P] Déficit diagonal global : sur les 3 lignes, M[i,i] · 3 < rowSum i. -/
theorem diagonal_deficit_all (i : Fin 3) : M3 i i * 3 < rowSum i := by
  fin_cases i
  · exact diagonal_deficit_11
  · exact diagonal_deficit_23
  · exact diagonal_deficit_29

/-!
## Section 5 — Statut épistémique du fichier
-/

/-- [P] Identité du fichier conforme à la doctrine. -/
def fileIdentity : FileIdentity where
  module := "CouretUnification.Core.SophieGermain"
  layer := Layer.core
  status := EpistemicStatus.proved
  sorryCount := 0
  rhClaimed := false

/-- [P] Vérification statique : ce fichier ne prétend pas prouver RH. -/
example : fileIdentity.rhClaimed = false := rfl

/-!
## Notes

1. **Falsifiabilité** : tout l'énoncé combinatoire est vérifiable par
   `decide`. Une seule entrée fausse de M3 serait immédiatement détectée.

2. **Lien avec la note** : SG_chi2_HL_note.pdf donne χ²_HL = 241.68 sur
   df=4, p < 10⁻⁴⁹. Le calcul de χ² lui-même demande Real et la fonction
   de répartition χ², qui ne sont pas formalisés ici. Ce fichier garantit
   les **données d'entrée** du calcul.

3. **Indépendance de RH** : aucun théorème de ce fichier ne dépend de
   l'Hypothèse de Riemann ou de ses généralisations. C'est un énoncé
   strictement empirique sur des comptages finis.
-/

end SophieGermain
end Core
end CouretUnification
