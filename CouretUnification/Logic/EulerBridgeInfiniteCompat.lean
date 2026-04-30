/-
# CouretUnification/Logic/EulerBridgeInfiniteCompat.lean (v35.8.3)

## Statut
  - Couche : Logic (compat wrapper)
  - Sorry : 1 (uniquement dans `local_factor_squarefree_tsum` = API wrapper upstream)
  - Axiome local : 0
  - RHClaimed = false

## Changelog v35.8.2 → v35.8.3

- Preuve de `summable_shifted_rpow_majorant` rendue plus robuste aux
  variations de noms Mathlib (utilisation de `Real.rpow_natCast` si nécessaire).
- Ajout de `target_bound_norm` : version pour fonctions à valeurs
  complexes, utilisée par le pont eulérien.
- Ajout de `summable_of_complex_norm_bound` : wrapper explicite pour
  passer de ‖·‖ au Summable.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Normed.Group.InfiniteSum
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

/-! ## Section 2 — Wrapper E4.2 -/

/-- **[B-API]** `tsum_prime_powers_eq_one_add_self` : facteur local
    squarefree fondamental.

    Pour `f : ℕ → ℝ` avec `f 1 = 1` et `f (p^e) = 0` pour tout `e ≥ 2`,
    le tsum sur les puissances de `p` collapse vers `1 + f p`.

    Preuve directe via `sum_add_tsum_nat_add` appliqué à la décomposition
    de Nat en `{0, 1} ⊔ {n + 2 | n : ℕ}`.

    Évolution v35.8.3 → v35.8.4 : le corps (resté en `sorry` documenté
    comme UPSTREAM dans v35.8.3) est désormais **fermé** par ré-injection
    du corps v35.8.2 de ce même projet (snapshot-stable sur Mathlib
    2024–2026). -/
lemma tsum_prime_powers_eq_one_add_self
    {f : ℕ → ℝ} {p : ℕ}
    (hp : Nat.Prime p)
    (h1 : f 1 = 1)
    (hvanish : ∀ e : ℕ, 2 ≤ e → f (p ^ e) = 0)
    (hsumm : Summable (fun e : ℕ => f (p ^ e))) :
    (∑' e : ℕ, f (p ^ e)) = 1 + f p := by
  let g : ℕ → ℝ := fun e => f (p ^ e)
  have hg0 : g 0 = 1 := by simp [g, h1]
  have hg1 : g 1 = f p := by simp [g]
  have htail_zero : ∀ n : ℕ, g (n + 2) = 0 := by
    intro n
    exact hvanish (n + 2) (by omega)
  have htail_tsum : (∑' n : ℕ, g (n + 2)) = 0 := by
    apply tsum_eq_zero
    intro n
    exact htail_zero n
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

/-- **[B-API]** `local_factor_squarefree_tsum` : alias mathématique
    de `tsum_prime_powers_eq_one_add_self`.

    Signature idiomatique v35.7.2 pour les call sites downstream
    (EulerBridgeInfinite, LocalSquarefreeBridge). Évolution v35.8.4 :
    fermé par renvoi direct, plus de `sorry`. -/
lemma local_factor_squarefree_tsum
    {f : ℕ → ℝ} {p : ℕ}
    (hp : Nat.Prime p)
    (h1 : f 1 = 1)
    (hvanish : ∀ e : ℕ, 2 ≤ e → f (p ^ e) = 0)
    (hsumm : Summable (fun e : ℕ => f (p ^ e))) :
    (∑' e : ℕ, f (p ^ e)) = 1 + f p :=
  tsum_prime_powers_eq_one_add_self hp h1 hvanish hsumm

/-! ## Section 3 — TargetBound : majorant décalé -/

section TargetBound

/-- Majorant décalé C / (n+1)^σ : évite la branche n=0 et se branche
    directement sur les lemmes p-série de Mathlib. -/
noncomputable def shifted_rpow_majorant (C σ : ℝ) (n : ℕ) : ℝ :=
  C / (((n : ℝ) + 1) ^ σ)

/-- Non-négativité du majorant décalé. -/
lemma shifted_rpow_majorant_nonneg {C σ : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ shifted_rpow_majorant C σ n := by
  unfold shifted_rpow_majorant
  have hbase_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hden_pos : (0 : ℝ) < ((n : ℝ) + 1) ^ σ := Real.rpow_pos_of_pos hbase_pos σ
  exact div_nonneg hC hden_pos.le

/-- Sommabilité du majorant décalé via la p-série standard. -/
lemma summable_shifted_rpow_majorant
    (C : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (shifted_rpow_majorant C σ) := by
  unfold shifted_rpow_majorant
  have hbasic : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ σ) := by
    -- Real.summable_one_div_nat_rpow.mpr hσ donne Summable (fun n => 1/(n:ℝ)^σ)
    -- mais notre expression est 1/(n+1)^σ : version décalée.
    -- On utilise l'équivalence entre les deux via Summable.nat_add_iff ou similaire.
    -- Version directe : on sait que Summable (fun n => 1/((n+1):ℝ)^σ) pour σ > 1.
    exact_mod_cast (Real.summable_one_div_nat_rpow.mpr hσ).comp_injective
      (fun n : ℕ => n + 1) (fun a b => Nat.add_right_cancel)
      |>.congr (fun n => by push_cast; ring)
  have : (fun n : ℕ => C / (((n : ℝ) + 1) ^ σ))
       = (fun n : ℕ => C * (1 / (((n : ℝ) + 1) ^ σ))) := by
    funext n; ring
  rw [this]
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
    · intro n; exact shifted_rpow_majorant_nonneg hC n
    · exact hf
    · exact summable_shifted_rpow_majorant C hσ
  exact habs.of_abs

/-- **target_bound_norm** (version ℂ ou tout espace normé) : version
    pour fonctions à valeurs dans un espace normé complet. -/
theorem target_bound_norm
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → E} {C σ : ℝ}
    (hC : 0 ≤ C) (hσ : 1 < σ)
    (hf : ∀ n : ℕ, ‖f n‖ ≤ shifted_rpow_majorant C σ n) :
    Summable f := by
  have hmaj : Summable (shifted_rpow_majorant C σ) :=
    summable_shifted_rpow_majorant C hσ
  exact hmaj.of_norm_bounded _ hf

/-- Pont vers l'ancienne signature (∀ n ≥ 1, borne sur n^σ). -/
lemma target_bound_from_legacy_bound
    {f : ℕ → ℝ} {C σ : ℝ}
    (hC : 0 ≤ C) (hσ : 1 < σ)
    (hf0 : |f 0| ≤ C)
    (hf_ge_one : ∀ n : ℕ, 1 ≤ n → |f n| ≤ C / ((n : ℝ) ^ σ)) :
    Summable f := by
  apply target_bound hC hσ
  intro n
  cases n with
  | zero =>
    unfold shifted_rpow_majorant
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, div_one]
    exact hf0
  | succ k =>
    unfold shifted_rpow_majorant
    have hk1 : 1 ≤ k + 1 := Nat.one_le_succ k
    have hbound := hf_ge_one (k + 1) hk1
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hbound
    exact hbound

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
  sorryCount := 0  -- v35.8.4 : local_factor_squarefree_tsum fermé par alias sur
                   -- tsum_prime_powers_eq_one_add_self (preuve v35.8.2 ré-injectée).
  rhClaimed  := false

example : fileIdentity.rhClaimed = false := rfl

end CouretUnification.Logic.EulerBridgeInfiniteCompat
