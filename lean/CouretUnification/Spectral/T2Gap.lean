import CouretUnification.Spectral.FiniteCore
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace CouretUnification
namespace T2Gap

open FiniteCore

/-!
# T2Gap

This file packages the finite-core coercive inequality into the abstract
`HasTargetGap` formulation used by the T2 layer.

Logical route:
1. define the coercive sector (`CoerciveSector`);
2. define the canonical data (`canonicalT2Data`);
3. express the target gap as an abstract proposition (`HasTargetGap`);
4. show that this proposition is equivalent to a concrete sector bound;
5. import the finite-core lower bound and conclude `HasTargetGap`.
-/

/-!
## 1. Coercive sector
-/

/-- Coercive sector: centered vectors orthogonal to `altVec`. -/
def CoerciveSector : Type :=
  { x : Centered8 // GoodSubspace x }

namespace CoerciveSector

/-- Underlying centered vector. -/
def val (x : CoerciveSector) : Centered8 := x.1

/-- Squared norm inherited from `Centered8`. -/
def normSq (x : CoerciveSector) : ℝ := x.1.normSq

/-- Energy induced by the finite-core quadratic form. -/
def energy (x : CoerciveSector) : ℝ := quadratic x.1.1

theorem normSq_nonneg (x : CoerciveSector) : 0 ≤ x.normSq := by
  exact x.1.normSq_nonneg

end CoerciveSector

/-!
## 2. Canonical T2 data
-/

/-- Formal gap constant kept as the target constant of the Couret programme. -/
def kappa : ℝ := 2

theorem kappa_pos : 0 < kappa := by
  unfold kappa
  norm_num

/-- Minimal T2 data wrapper for the lightweight stage. -/
structure T2Data where
  Q : CoerciveSector → ℝ
  κ : ℝ
  κ_pos : 0 < κ

/-- Canonical energy data induced by the finite core. -/
def canonicalT2Data : T2Data :=
  { Q := CoerciveSector.energy
    κ := kappa
    κ_pos := kappa_pos }

/-- Generic gap statement attached to a `T2Data` package. -/
def GapStatementFor (T : T2Data) : Prop :=
  ∀ x : CoerciveSector, T.κ * x.normSq ≤ T.Q x

theorem canonical_gap_statement_def :
    GapStatementFor canonicalT2Data =
      ∀ x : CoerciveSector, kappa * x.normSq ≤ x.energy := by
  rfl

/-!
## 3. Abstract target proposition
-/

/-- Abstract coercive-gap predicate on the current sector. -/
def HasAbstractGap (κ : ℝ) : Prop :=
  ∀ x : CoerciveSector, κ * x.normSq ≤ x.energy

/-- The target coercive statement for the programme. -/
def HasTargetGap : Prop :=
  HasAbstractGap kappa

theorem HasTargetGap_def :
    HasTargetGap = HasAbstractGap kappa := by
  rfl

theorem energy_def_on_sector (x : CoerciveSector) :
    CoerciveSector.energy x = quadratic x.1.1 := by
  rfl

theorem normSq_def_on_sector (x : CoerciveSector) :
    CoerciveSector.normSq x = x.1.normSq := by
  rfl

theorem canonicalT2Data_Q (x : CoerciveSector) :
    canonicalT2Data.Q x = CoerciveSector.energy x := by
  rfl

theorem canonicalT2Data_kappa :
    canonicalT2Data.κ = kappa := by
  rfl

/-!
## 4. Optional packaging of a proof object
-/

structure GapData where
  proof : HasTargetGap

def HasCanonicalGapData : Prop := Nonempty GapData

theorem HasCanonicalGapData_def :
    HasCanonicalGapData ↔ Nonempty GapData := by
  rfl

theorem gapData_implies_target (h : GapData) : HasTargetGap := by
  exact h.proof

def mkGapData (h : HasTargetGap) : GapData := ⟨h⟩

theorem mkGapData_spec (h : HasTargetGap) :
    (mkGapData h).proof = h := by
  rfl

theorem target_of_canonical_gap (h : HasCanonicalGapData) : HasTargetGap := by
  rcases h with ⟨g⟩
  exact gapData_implies_target g

theorem canonicalGapData_of_targetGap (h : HasTargetGap) :
    HasCanonicalGapData := by
  exact ⟨mkGapData h⟩

/-!
## 5. Equivalences between formulations
-/

theorem hasTargetGap_iff_canonicalGapStatement :
    HasTargetGap ↔ GapStatementFor canonicalT2Data := by
  rfl

theorem canonical_gap_statement_explicit :
    GapStatementFor canonicalT2Data ↔
      ∀ x : CoerciveSector, 2 * x.normSq ≤ x.energy := by
  rw [canonical_gap_statement_def]
  rfl

/-- Sector vectors are orthogonal to `altVec` by construction. -/
theorem dot_altVec_zero_of_sector (x : CoerciveSector) :
    dot x.1.1 altVec = 0 := by
  exact (goodSubspace_iff_dot_altVec_zero x.1).1 x.2

/-- A canonical gap statement yields the concrete lower bound on each sector vector. -/
theorem canonical_gap_statement_on_sector (x : CoerciveSector) :
    GapStatementFor canonicalT2Data →
    2 * x.normSq ≤ quadratic x.1.1 := by
  intro h
  have hx : 2 * x.normSq ≤ x.energy := by
    exact (canonical_gap_statement_explicit.mp h) x
  simpa [normSq_def_on_sector, energy_def_on_sector] using hx

/-- Conversely, a concrete lower bound on the sector yields the canonical gap statement. -/
theorem canonical_gap_statement_of_sector_bound
    (h : ∀ x : CoerciveSector, 2 * x.normSq ≤ quadratic x.1.1) :
    GapStatementFor canonicalT2Data := by
  rw [canonical_gap_statement_explicit]
  intro x
  simpa [normSq_def_on_sector, energy_def_on_sector] using h x

/-- Main equivalence between the canonical gap statement and the explicit sector bound. -/
theorem canonical_gap_statement_iff_sector_bound :
    GapStatementFor canonicalT2Data ↔
      ∀ x : CoerciveSector, 2 * x.normSq ≤ quadratic x.1.1 := by
  constructor
  · intro h x
    exact canonical_gap_statement_on_sector x h
  · intro h
    exact canonical_gap_statement_of_sector_bound h

/-- Reformulation of `HasTargetGap` as the explicit sector inequality. -/
theorem hasTargetGap_iff_sector_bound :
    HasTargetGap ↔ ∀ x : CoerciveSector, 2 * x.normSq ≤ quadratic x.1.1 := by
  rw [hasTargetGap_iff_canonicalGapStatement]
  exact canonical_gap_statement_iff_sector_bound

/-- Same target reformulation, written in the exact shape often used as a goal. -/
theorem sector_bound_goal_form :
    HasTargetGap ↔
      ∀ x : CoerciveSector, 2 * x.1.normSq ≤ quadratic x.1.1 := by
  simpa using hasTargetGap_iff_sector_bound

/-!
## 6. Import from `FiniteCore`
-/

/-- Finite-core coercive inequality, transported to the coercive sector. -/
theorem quadratic_lower_bound_on_sector (x : CoerciveSector) :
    2 * x.normSq ≤ quadratic x.1.1 := by
  simpa using quadratic_lower_bound_on_goodSubspace x.1 x.2

/-- The target gap is proved by the finite-core lower bound. -/
theorem hasTargetGap_proved : HasTargetGap := by
  rw [hasTargetGap_iff_sector_bound]
  intro x
  simpa using quadratic_lower_bound_on_sector x

/-- Final exported bridge from the finite core to the abstract T2 target. -/
theorem hasTargetGap_from_finiteCore :
  HasTargetGap := hasTargetGap_proved

/-!
## Exact coercive gap (exported from the finite core)
-/

/-- Exact coercive gap at κ = 2, inherited from the finite core. -/
theorem exact_coercive_gap_kappa_two :
    HasTargetGap := by
  exact hasTargetGap_from_finiteCore

/-- Explicit coercive inequality on the sector. -/
theorem exact_coercive_gap_kappa_two_explicit :
    ∀ x : CoerciveSector, 2 * x.normSq ≤ x.energy := by
  intro x
  exact (canonical_gap_statement_explicit.mp exact_coercive_gap_kappa_two) x

end T2Gap
end CouretUnification
