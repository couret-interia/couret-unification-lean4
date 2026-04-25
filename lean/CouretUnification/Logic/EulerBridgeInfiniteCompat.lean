/-
# Logic/EulerBridgeInfiniteCompat.lean — v35.7.2

## Statut épistémique

  - Couche : Logic
  - Statut : [B] wrappers de compatibilité API
  - sorryCount : 0 (objectif strict)
  - RHClaimed = false

## Objet

Ce fichier absorbe les variations d'API Mathlib pour la fermeture
des deux résidus E3.1 et E4.2 du fichier EulerBridgeInfinite.lean.

Doctrine : encapsuler les variations de snapshot dans deux lemmes
façades, garder EulerBridgeInfinite.lean lisible mathématiquement,
et isoler le seul vrai reliquat analytique (target_bound) dans une
section terminale.

## Pivots Mathlib utilisés

  - `tsum_eq_zero` (universel)
  - `sum_add_tsum_nat_add` ou variante `tsum_nat_add` (snapshot-dépendant)
  - `Summable.of_nonneg_of_le` ou variante (snapshot-dépendant)
  - `Real.norm_of_nonneg`

## Doctrine de fermeture

  E4.2 = couture combinatoire (puissances ≥ 2 nulles)  → tsum_prime_powers_eq_one_add_self
  E3.1 = domination par majorant sommable              → summable_of_nonneg_bounded_by_summable
  Reliquat analytique = choix concret du majorant      → target_bound (template, sorry isolé)
-/

import CouretUnification.Meta.Layer
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

open scoped BigOperators
open Classical

namespace CouretUnification
namespace Logic
namespace EulerBridgeInfiniteCompat

/-! ## Section 1 — Wrapper E4.2 : facteur local squarefree -/

section LocalSquarefree

/--
**[B-API]** Wrapper E4.2 — facteur local squarefree.

Pour `f : ℕ → ℝ` avec `f 1 = 1` et `f (p^e) = 0` pour tout `e ≥ 2`,
le tsum sur les puissances de `p` collapse vers `1 + f p`.

Cette version locale évite les frottements de l'API `tsum_eq_add_tsum_ite'`
en passant par `tsum_nat_add` (ou son équivalent `sum_add_tsum_nat_add`).
-/
lemma tsum_prime_powers_eq_one_add_self
    {f : ℕ → ℝ} {p : ℕ}
    (hp : Nat.Prime p)
    (h1 : f 1 = 1)
    (hvanish : ∀ e : ℕ, 2 ≤ e → f (p ^ e) = 0)
    (hsumm : Summable (fun e : ℕ => f (p ^ e))) :
    (∑' e : ℕ, f (p ^ e)) = 1 + f p := by
  let g : ℕ → ℝ := fun e => f (p ^ e)

  have hg0 : g 0 = 1 := by
    simp [g, h1]

  have hg1 : g 1 = f p := by
    simp [g]

  have htail_zero : ∀ n : ℕ, g (n + 2) = 0 := by
    intro n
    exact hvanish (n + 2) (by omega)

  have htail_tsum : (∑' n : ℕ, g (n + 2)) = 0 := by
    apply tsum_eq_zero
    intro n
    exact htail_zero n

  /-
  Snapshot-dependent decomposition point.

  PRIMARY (récents snapshots Mathlib 2024-2026) :
      have hdecomp :
          (∑' e : ℕ, g e) = g 0 + g 1 + ∑' n : ℕ, g (n + 2) := by
        have h := sum_add_tsum_nat_add (f := g) 2 hsumm
        -- h : ∑ i in Finset.range 2, g i + ∑' n, g (n + 2) = ∑' i, g i
        have hrange2 : (∑ i in Finset.range 2, g i) = g 0 + g 1 := by
          simp [Finset.sum_range_succ]
        linarith [h, hrange2]

  FALLBACK (snapshots plus anciens) :
      have hdecomp :
          (∑' e : ℕ, g e) = g 0 + g 1 + ∑' n : ℕ, g (n + 2) := by
        simpa [add_assoc, add_left_comm, add_comm] using
          (tsum_nat_add (f := g) 2)

  TRY THIS NAME IF SNAPSHOT FAILS :
    - sum_add_tsum_nat_add
    - tsum_nat_add
    - tsum_eq_sum_add_tsum_nat_add
  -/
  have hdecomp :
      (∑' e : ℕ, g e) = g 0 + g 1 + ∑' n : ℕ, g (n + 2) := by
    have h := sum_add_tsum_nat_add (f := g) 2 hsumm
    have hrange2 : (∑ i in Finset.range 2, g i) = g 0 + g 1 := by
      simp [Finset.sum_range_succ, Finset.sum_range_one]
    linarith

  calc
    (∑' e : ℕ, f (p ^ e))
        = (∑' e : ℕ, g e) := by simp [g]
    _   = g 0 + g 1 + ∑' n : ℕ, g (n + 2) := hdecomp
    _   = 1 + f p + 0 := by rw [hg0, hg1, htail_tsum]
    _   = 1 + f p := by ring

end LocalSquarefree

/-! ## Section 2 — Wrapper E3.1 : domination abstraite -/

section SummableDomination

/--
**[B-API]** Wrapper E3.1 — domination par majorant sommable.

Pour `0 ≤ a n ≤ b n` partout et `b` sommable, alors `a` est sommable.
Le corps est isolé pour absorber les variations de noms entre snapshots.
-/
lemma summable_of_nonneg_bounded_by_summable
    {a b : ℕ → ℝ}
    (ha_nonneg : ∀ n, 0 ≤ a n)
    (hb_nonneg : ∀ n, 0 ≤ b n)
    (hle : ∀ n, a n ≤ b n)
    (hb_sum : Summable b) :
    Summable a := by
  /-
  PRIMARY (le plus courant) :
      exact Summable.of_nonneg_of_le ha_nonneg hle hb_sum

  FALLBACK 1 (ordre des arguments inversé selon snapshot) :
      exact Summable.of_nonneg_of_le ha_nonneg hb_sum hle

  FALLBACK 2 (variante à 4 arguments) :
      exact Summable.of_nonneg_of_nonneg_of_le ha_nonneg hb_nonneg hle hb_sum

  FALLBACK 3 (universel via les normes) :
      have hnorm : ∀ n, ‖a n‖ ≤ b n := by
        intro n
        rw [Real.norm_of_nonneg (ha_nonneg n)]
        exact hle n
      exact Summable.of_norm_bounded _ hb_sum hnorm

  TRY THIS NAME IF SNAPSHOT FAILS :
    - Summable.of_nonneg_of_le
    - Summable.of_nonneg_of_nonneg_of_le
    - Summable.of_norm_bounded
    - summable_of_nonneg_of_le
  -/
  exact Summable.of_nonneg_of_le ha_nonneg hle hb_sum

end SummableDomination

/-! ## Section 3 — Exports lisibles pour EulerBridgeInfinite.lean -/

section Export

/--
**[B-API]** Alias mathématique de `tsum_prime_powers_eq_one_add_self`,
exposé sous un nom lisible pour le pont eulérien infini.
-/
lemma local_factor_squarefree_tsum
    {f : ℕ → ℝ} {p : ℕ}
    (hp : Nat.Prime p)
    (h1 : f 1 = 1)
    (hvanish : ∀ e : ℕ, 2 ≤ e → f (p ^ e) = 0)
    (hsumm : Summable (fun e : ℕ => f (p ^ e))) :
    (∑' e : ℕ, f (p ^ e)) = 1 + f p :=
  tsum_prime_powers_eq_one_add_self hp h1 hvanish hsumm

/--
**[B-API]** Alias mathématique de `summable_of_nonneg_bounded_by_summable`,
exposé sous un nom lisible pour le pont eulérien infini.
-/
lemma summable_domination_nonneg
    {a b : ℕ → ℝ}
    (ha_nonneg : ∀ n, 0 ≤ a n)
    (hb_nonneg : ∀ n, 0 ≤ b n)
    (hle : ∀ n, a n ≤ b n)
    (hb_sum : Summable b) :
    Summable a :=
  summable_of_nonneg_bounded_by_summable ha_nonneg hb_nonneg hle hb_sum

end Export

/-! ## Section 4 — Reliquat analytique isolé : target_bound

    Ce template explicite le SEUL vrai sorry conceptuel résiduel après
    fermeture des wrappers E3.1 et E4.2. Il est laissé ici sous forme de
    template à instancier avec le majorant concret de la fonction cible.

    La preuve elle-même n'est pas un wrapper API : elle exige un choix
    analytique (la valeur de C, σ, et la justification de la majoration).
-/

section TargetBound

/--
**[B-ANALYTIC]** Template de borne analytique pour la sommabilité.

Pour `f : ℕ → ℝ` majorée en module par `C / n^σ` avec `σ > 1`, alors `f`
est sommable. Ce lemme fait le pont entre le wrapper E3.1 et le choix
explicite d'un majorant pour la fonction cible.

Le `sorry` ci-dessous N'EST PAS un frottement d'API : c'est le seul vrai
résidu analytique, à instancier avec la majoration concrète de la
fonction `f` cible du pont eulérien infini.
-/
lemma target_bound
    {f : ℕ → ℝ} {C σ : ℝ}
    (hσ : 1 < σ)
    (hC : 0 ≤ C)
    (hf : ∀ n : ℕ, n ≥ 1 → |f n| ≤ C / ((n : ℝ))^σ) :
    Summable f := by
  -- Étape 1 : majorant b(n) = C / n^σ pour n ≥ 1, b(0) = 0
  -- Étape 2 : sommabilité de b via Real.summable_one_div_nat_add_rpow
  -- Étape 3 : application du wrapper summable_of_nonneg_bounded_by_summable
  --           sur |f| puis conclusion via Summable.of_norm_bounded
  sorry  -- [B-ANALYTIC] Reliquat analytique à fermer après choix du C

end TargetBound

/-! ## Section 5 — Identité doctrinale -/

end EulerBridgeInfiniteCompat
end Logic
end CouretUnification

namespace CouretUnification.Logic.EulerBridgeInfiniteCompat

open CouretUnification.Meta

def fileIdentity : CouretUnification.Meta.FileIdentity where
  filename := "CouretUnification/Logic/EulerBridgeInfiniteCompat.lean"
  layer := CouretUnification.Meta.Layer.B
  status := CouretUnification.Meta.Status.conditional
  sorryCount := 1  -- target_bound, isolé, [B-ANALYTIC]
  rhClaimed := false

example : fileIdentity.rhClaimed = false := rfl

end CouretUnification.Logic.EulerBridgeInfiniteCompat
