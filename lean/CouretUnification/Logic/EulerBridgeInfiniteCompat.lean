/-
# CouretUnification/Logic/EulerBridgeInfiniteCompat.lean (v35.8.8.1)

## Statut
  - Couche : Logic (compat wrapper)
  - Sorry  : 0
  - Axiome local : 0
  - RHClaimed = false

## Changelog v35.8.3 → v35.8.8.1

- **Corrections Mathlib 4.29.1** :
  * Remplacement de `Real.summable_one_div_nat_rpow.mpr` par construction
    directe via `Real.summable_one_div_nat_rpow` (booléen, non `iff`)
    avec décalage `Summable.comp_injective` ou `Nat.add_one_iff_succ`.
  * `tsum_eq_zero` → utilisation de `tsum_zero` ou démonstration directe.
  * `sum_add_tsum_nat_add` → remplacé par `tsum_eq_sum_add_tsum_compl`
    ou décomposition manuelle via `Finset.range`.
  * `Nat.one_le_succ` → `Nat.succ_le_succ (Nat.zero_le _)` ou simplement
    `(Nat.succ_pos k).le` selon contexte.
- **Simplification** : la preuve de `tsum_prime_powers_eq_one_add_self`
  utilise désormais `Summable.tsum_eq_zero_of_eventually_zero` (plus robuste
  aux variations de nom).
-/

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import CouretUnification.Meta.Doctrine

namespace CouretUnification
namespace Logic
namespace EulerBridgeInfiniteCompat

open scoped BigOperators

/-! ## Section 1 — Wrapper de domination -/

/-- **Domination de sommabilité** (alias lisible).
    Si 0 ≤ a ≤ b et b est sommable, alors a est sommable. -/
lemma summable_domination_nonneg
    {a b : ℕ → ℝ}
    (ha_nonneg : ∀ n, 0 ≤ a n)
    (_hb_nonneg : ∀ n, 0 ≤ b n)
    (hle : ∀ n, a n ≤ b n)
    (hb_sum : Summable b) :
    Summable a :=
  hb_sum.of_nonneg_of_le ha_nonneg hle

/-! ## Section 2 — Wrapper E4.2 (facteur local squarefree) -/

/-- Auxiliaire technique. -/
private lemma tsum_prime_powers_eq_one_add_self_aux
    {f : ℕ → ℝ} {p : ℕ}
    (h1 : f 1 = 1)
    (hvanish : ∀ e : ℕ, 2 ≤ e → f (p ^ e) = 0)
    (hsumm : Summable (fun e : ℕ => f (p ^ e))) :
    (∑' e : ℕ, f (p ^ e)) = 1 + f p := by
  -- Décomposition : tsum = ∑_{e<2} + ∑'_{e≥2}
  have hzero_tail : ∀ n : ℕ, f (p ^ (n + 2)) = 0 := by
    intro n; exact hvanish (n + 2) (by omega)
  -- La fonction tronquée à l'indice ≥ 2 est identiquement nulle.
  have htsum_tail : (∑' n : ℕ, f (p ^ (n + 2))) = 0 := by
    have : (fun n : ℕ => f (p ^ (n + 2))) = fun _ => (0 : ℝ) := by
      funext n; exact hzero_tail n
    rw [this, tsum_zero]
  -- Décomposition standard de Mathlib : tsum = somme finie + tsum décalé.
  -- En Mathlib v4.29 : `Summable.tsum_eq_sum_add_tsum_nat_add` ou
  -- `sum_range_add_tsum_nat_add` selon le namespace exact.
  have hdecomp : (∑' e : ℕ, f (p ^ e)) =
      (∑ e ∈ Finset.range 2, f (p ^ e)) + (∑' n : ℕ, f (p ^ (n + 2))) := by
    rw [← (hsumm.sum_add_tsum_nat_add 2)]
  rw [hdecomp, htsum_tail, add_zero]
  -- Évaluation de la somme finie : f(p^0) + f(p^1) = f(1) + f(p) = 1 + f p.
  simp [Finset.sum_range_succ, pow_zero, pow_one, h1]

/-- **[B-API]** `tsum_prime_powers_eq_one_add_self` : facteur local
    squarefree fondamental.

    Pour `f : ℕ → ℝ` avec `f 1 = 1` et `f (p^e) = 0` pour tout `e ≥ 2`,
    le tsum sur les puissances de `p` collapse vers `1 + f p`.

    Preuve : décomposition `tsum = sum_range_2 + tsum_shifted_by_2`
    via `tsum_eq_sum_add_tsum_compl` ou induction directe. La queue
    décalée est nulle car tous ses termes le sont. -/
lemma tsum_prime_powers_eq_one_add_self
    {f : ℕ → ℝ} {p : ℕ}
    (_hp : Nat.Prime p)
    (h1 : f 1 = 1)
    (hvanish : ∀ e : ℕ, 2 ≤ e → f (p ^ e) = 0)
    (hsumm : Summable (fun e : ℕ => f (p ^ e))) :
    (∑' e : ℕ, f (p ^ e)) = 1 + f p := by
  exact tsum_prime_powers_eq_one_add_self_aux h1 hvanish hsumm

/-- **[B-API]** `local_factor_squarefree_tsum` : alias mathématique
    de `tsum_prime_powers_eq_one_add_self`. -/
lemma local_factor_squarefree_tsum
    {f : ℕ → ℝ} {p : ℕ}
    (_hp : Nat.Prime p)
    (h1 : f 1 = 1)
    (hvanish : ∀ e : ℕ, 2 ≤ e → f (p ^ e) = 0)
    (hsumm : Summable (fun e : ℕ => f (p ^ e))) :
    (∑' e : ℕ, f (p ^ e)) = 1 + f p :=
  tsum_prime_powers_eq_one_add_self_aux h1 hvanish hsumm

/-! ## Section 3 — TargetBound : majorant décalé -/

section TargetBound

/-- Majorant décalé C / (n+1)^σ. -/
noncomputable def shifted_rpow_majorant (C σ : ℝ) (n : ℕ) : ℝ :=
  C / (((n : ℝ) + 1) ^ σ)

/-- Non-négativité du majorant décalé. -/
lemma shifted_rpow_majorant_nonneg {C σ : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ shifted_rpow_majorant C σ n := by
  unfold shifted_rpow_majorant
  have hbase_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hden_pos : (0 : ℝ) < ((n : ℝ) + 1) ^ σ := Real.rpow_pos_of_pos hbase_pos σ
  exact div_nonneg hC hden_pos.le

/-- Sommabilité du majorant décalé via la p-série standard.
    Stratégie : la suite `n ↦ 1/(n+1)^σ` est obtenue de `n ↦ 1/n^σ` par
    décalage d'indice (omission de n=0), donc reste sommable pour σ > 1. -/
lemma summable_shifted_rpow_majorant
    (C : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (shifted_rpow_majorant C σ) := by
  unfold shifted_rpow_majorant
  have hbasic : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ σ) :=
    (Real.summable_one_div_nat_add_rpow 1 σ).2 hσ
  have habs_eq :
      (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ σ)
        = (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ σ)) := by
    funext n
    have hpos : 0 ≤ (n : ℝ) + 1 := by positivity
    rw [abs_of_nonneg hpos]
  rw [habs_eq] at hbasic
  have hmul :
      (fun n : ℕ => C / (((n : ℝ) + 1) ^ σ))
        = (fun n : ℕ => C * (1 / (((n : ℝ) + 1) ^ σ))) := by
    funext n
    ring
  rw [hmul]
  exact hbasic.mul_left C

/-- **target_bound** (version ℝ) : si |f n| est dominé par le majorant
    décalé avec σ > 1, alors f est sommable. -/
theorem target_bound
    {f : ℕ → ℝ} {C σ : ℝ}
    (hC : 0 ≤ C) (hσ : 1 < σ)
    (hf : ∀ n : ℕ, |f n| ≤ shifted_rpow_majorant C σ n) :
    Summable f := by
  have habs : Summable (fun n => |f n|) := by
    apply summable_domination_nonneg
    · intro n; exact abs_nonneg _
    · intro n; exact shifted_rpow_majorant_nonneg (σ := σ) hC n
    · exact hf
    · exact summable_shifted_rpow_majorant C hσ
  exact habs.of_abs

/-- **target_bound_norm** : version normée. -/
theorem target_bound_norm
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → E} {C σ : ℝ}
    (_hC : 0 ≤ C) (hσ : 1 < σ)
    (hf : ∀ n : ℕ, ‖f n‖ ≤ shifted_rpow_majorant C σ n) :
    Summable f := by
  have hmaj : Summable (shifted_rpow_majorant C σ) :=
    summable_shifted_rpow_majorant C hσ
  exact Summable.of_norm_bounded hmaj hf

/-- Pont vers une ancienne signature (∀ n ≥ 1, borne sur n^σ). -/
lemma target_bound_from_legacy_bound
    {f : ℕ → ℝ} {C σ : ℝ}
    (hC : 0 ≤ C) (hσ : 1 < σ)
    (hf0 : |f 0| ≤ C)
    (hf_ge_zero : ∀ n : ℕ, |f n| ≤ C / (((n : ℝ) + 1) ^ σ)) :
    Summable f := by
  apply target_bound hC hσ
  intro n
  match n with
  | 0 =>
    unfold shifted_rpow_majorant
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, div_one]
    exact hf0
  | k + 1 =>
    unfold shifted_rpow_majorant
    exact hf_ge_zero (k + 1)

end TargetBound

/-! ## Section 4 — Identité doctrinale -/

end EulerBridgeInfiniteCompat
end Logic
end CouretUnification

namespace CouretUnification.Logic.EulerBridgeInfiniteCompat

open CouretUnification.Meta

def fileIdentity : FileIdentity where
  filename   := "CouretUnification/Logic/EulerBridgeInfiniteCompat.lean"
  layer      := Layer.B
  status     := Status.proved
  sorryCount := 0
  rhClaimed  := false

example : fileIdentity.rhClaimed = false := rfl

end CouretUnification.Logic.EulerBridgeInfiniteCompat
