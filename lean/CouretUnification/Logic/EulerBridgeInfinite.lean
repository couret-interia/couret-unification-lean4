/-
# Logic/EulerBridgeInfinite.lean — E3/E4 via Mathlib EulerProduct (v38.5.5)

## Statut épistémique

  - Couche : Logic
  - Statut : [D] prouvé.
  - sorryCount : 0
  - RHClaimed : false

## Refactoring v35.7.1

Cette version remplace la précédente par un découpage plus serré, avec
lemmes numérotés selon la structure conceptuelle :

  - E4.1 : annulation locale sur les puissances premières élevées (trivial, 0 sorry)
  - E4.2 : facteur local squarefree `∑' e, f(p^e) = 1 + f p`     ← [PROVED]
  - E3.1 : comparaison abstraite par majorant sommable           ← [PROVED]
  - E3.2 : majoration pratique par p-série décalée (preuve complète)
  - e4_bridge_tprod : pont EulerProduct standard (preuve complète)
  - squarefree_limit_eq_euler_product : théorème final (preuve complète)

Le cœur mathématique propre du fichier est minuscule : E4.2 et E3.1.
Tout le reste est plomberie qui s'appuie sur Mathlib.

## Doctrine — Recentrage E3/E4 vs stratégie bespoke

Avant v35.7, E3/E4 étaient envisagés comme un long argument bespoke
"fini → infini". Le pivot Mathlib `EulerProduct.eulerProduct_tprod`
rend cette construction inutile :

  - **E4** = couture locale élémentaire (puissances ≥ 2 nulles).
  - **E3** = sommabilité de `n ↦ ‖f n‖` par domination via p-série.
  - **Pont infini** = appel direct à `EulerProduct.eulerProduct_tprod`.

## Pivots Mathlib utilisés

  - `Mathlib.NumberTheory.EulerProduct.Basic`
      → `EulerProduct.eulerProduct_tprod`
  - `Mathlib.Analysis.PSeries`
      → `Real.summable_one_div_nat_add_rpow`
  - `Mathlib.Topology.Algebra.InfiniteSum.Basic`
      → `tprod_congr`
-/

import CouretUnification.Logic.Doctrine
import CouretUnification.Logic.H3.SquarefreeSupport
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

noncomputable section
open scoped BigOperators
open Classical

namespace CouretUnification.Logic.EulerBridgeInfinite

open CouretUnification.Meta

/-! ## Section 1 — Hypothèse de support squarefree -/

/-- **[B] Support squarefree abstrait.**

    Une fonction `f : ℕ → R` est dite "squarefree-supportée" si elle
    s'annule sur toute puissance première d'exposant ≥ 2. -/
def SquarefreeSupportLike {R : Type*} [Zero R] (f : ℕ → R) : Prop :=
  ∀ {p e : ℕ}, Nat.Prime p → 2 ≤ e → f (p ^ e) = 0

/-! ## Section 2 — Lemmes E4 (couture locale) -/

section E4Local

variable {R : Type*} [Zero R]

/-- **[A] E4.1 : annulation locale sur les puissances premières élevées.**

    Conséquence directe et triviale de `SquarefreeSupportLike`. Pas de sorry.

    Ce lemme est purement algébrique : il ne requiert ni norme, ni complétude.
-/
lemma e4_1_prime_pow_eq_zero
    (f : ℕ → R)
    (hsf : SquarefreeSupportLike f)
    {p e : ℕ} (hp : Nat.Prime p) (he : 2 ≤ e) :
    f (p ^ e) = 0 :=
  hsf hp he

end E4Local

section Analytic

variable {R : Type*} [NormedCommRing R] [CompleteSpace R]

omit [CompleteSpace R] in
/-- **[D] E4.2 : facteur local squarefree.**

    Pour `f` squarefree-supportée avec `f 1 = 1`, on a
        `∑' e, f (p^e) = 1 + f p`.

    Preuve conceptuelle : termes `e=0` (= 1) + `e=1` (= f p) + queue nulle. -/
lemma e4_2_prime_pow_tsum_eq_one_add
    (f : ℕ → R)
    (hf1 : f 1 = 1)
    (hsf : SquarefreeSupportLike f)
    {p : ℕ} (hp : Nat.Prime p) :
    (∑' e : ℕ, f (p ^ e)) = 1 + f p := by
  classical
  calc
    (∑' e : ℕ, f (p ^ e))
        = Finset.sum ({0, 1} : Finset ℕ) (fun e => f (p ^ e)) := by
            exact tsum_eq_sum
              (f := fun e : ℕ => f (p ^ e))
              (s := ({0, 1} : Finset ℕ))
              (by
                intro e he
                have he0 : e ≠ 0 := by
                  intro h
                  exact he (by simp [h])
                have he1 : e ≠ 1 := by
                  intro h
                  exact he (by simp [h])
                have he2 : 2 ≤ e := by
                  omega
                exact hsf hp he2)
    _ = 1 + f p := by
            simp [hf1]

/-! ## Section 3 — Lemmes E3 (sommabilité analytique) -/

omit [CompleteSpace R] in
/-- **[A] E3.1 : comparaison abstraite par un majorant sommable.**

    Si `‖f n‖ ≤ majorant n` avec `majorant ≥ 0` et `Summable majorant`,
    alors `Summable (fun n => ‖f n‖)`. -/
lemma e3_1_summable_norm_of_domination
    (f : ℕ → R) (majorant : ℕ → ℝ)
    (_h_nonneg : ∀ n, 0 ≤ majorant n)
    (h_le : ∀ n, ‖f n‖ ≤ majorant n)
    (h_majorant : Summable majorant) :
    Summable (fun n : ℕ => ‖f n‖) := by
  exact Summable.of_nonneg_of_le
    (fun n => norm_nonneg (f n))
    h_le
    h_majorant

omit [CompleteSpace R] in
/-- **[A] E3.2 : majoration pratique par p-série décalée.**

    Si `‖f n‖ ≤ C / |n + a|^σ` avec `σ > 1` et `a ≥ 0`,
    alors `Summable (fun n => ‖f n‖)`.

    Preuve complète qui s'appuie sur `Real.summable_one_div_nat_add_rpow`
    et la comparaison E3.1. -/
lemma e3_2_summable_norm_of_nat_add_rpow_bound
    (f : ℕ → R) (C a σ : ℝ)
    (hC : 0 ≤ C)
    (hσ : 1 < σ)
    (_ha : 0 ≤ a)
    (hbound : ∀ n, ‖f n‖ ≤ C / |(n : ℝ) + a| ^ σ) :
    Summable (fun n : ℕ => ‖f n‖) := by
  have hbase : Summable (fun n : ℕ => 1 / |(n : ℝ) + a| ^ σ) :=
    (Real.summable_one_div_nat_add_rpow a σ).mpr hσ
  have hscaled : Summable (fun n : ℕ => C * (1 / |(n : ℝ) + a| ^ σ)) :=
    hbase.mul_left C
  refine e3_1_summable_norm_of_domination f
    (fun n => C * (1 / |(n : ℝ) + a| ^ σ))
    ?_ ?_ hscaled
  · intro n
    exact mul_nonneg hC (by positivity)
  · intro n
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hbound n

/-! ## Section 4 — Pont EulerProduct (pivot Mathlib) -/

/-- **[A] Pont EulerProduct standard, version `tprod`.**

    Wrapper direct sur `EulerProduct.eulerProduct_tprod`. Aucun contenu
    mathématique propre ; expose le théorème pivot dans le namespace du
    programme pour un appel localisé. -/
theorem e4_bridge_tprod
    (f : ℕ → R)
    (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : Summable (fun n : ℕ => ‖f n‖))
    (hf0 : f 0 = 0) :
    (∏' p : Nat.Primes, ∑' e : ℕ, f ((p : ℕ) ^ e)) = ∑' n : ℕ, f n := by
  simpa using EulerProduct.eulerProduct_tprod hf1 @hmul hsum hf0

/-! ## Section 5 — Théorème final E3/E4 -/

/-- **[D] E3+E4 final : produit eulérien linéarisé dans le cas squarefree.**

    Si `f` est squarefree-supportée, multiplicative sur coprimes, normée
    sommable, avec `f 0 = 0` et `f 1 = 1`, alors

        `∑' n, f n = ∏' p : Nat.Primes, (1 + f p)`.

    Preuve : couture locale E4.2 + pont EulerProduct standard. -/
theorem squarefree_limit_eq_euler_product
    (f : ℕ → R)
    (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : Summable (fun n : ℕ => ‖f n‖))
    (hf0 : f 0 = 0)
    (hsf : SquarefreeSupportLike f) :
    (∏' p : Nat.Primes, (1 + f (p : ℕ))) = ∑' n : ℕ, f n := by
  calc
    (∏' p : Nat.Primes, (1 + f (p : ℕ)))
      = ∏' p : Nat.Primes, ∑' e : ℕ, f ((p : ℕ) ^ e) := by
          refine tprod_congr ?_
          intro p
          symm
          exact e4_2_prime_pow_tsum_eq_one_add f hf1 hsf p.property
    _ = ∑' n : ℕ, f n := by
          simpa using e4_bridge_tprod f hf1 @hmul hsum hf0

end Analytic

/-! ## Section 7 — Identité doctrinale -/

def fileIdentity : CouretUnification.Meta.FileIdentity where
  filename := "CouretUnification/Logic/EulerBridgeInfinite.lean"
  layer := CouretUnification.Meta.Layer.B
  status := CouretUnification.Meta.Status.proved
  sorryCount := 0
  rhClaimed := false

example : fileIdentity.rhClaimed = false := rfl

end CouretUnification.Logic.EulerBridgeInfinite
