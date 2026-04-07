import CouretUnification.Spectral.FiniteCore
import CouretUnification.Spectral.T2Gap
import Mathlib.Data.Real.Basic

namespace CouretUnification
namespace H1Bridge

open FiniteCore
open T2Gap

/-!
# H1Bridge

This file packages the first finite bridge from the exact mod 30 core
toward a reduced coercive spectral interface.

It does **not** construct any global Hilbert--Pólya operator.
It only records the exact finite coercive structure already proved in
`FiniteCore.lean` and exported through `T2Gap.lean`.

The purpose of this layer is to isolate a clean “H1-type” object:
a reduced coercive sector equipped with an exact gap constant.
-/

/-- Minimal reduced coercive package extracted from the finite core. -/
structure ReducedCoerciveData where
  /-- Underlying reduced space. -/
  space : Type
  /-- Squared norm on the reduced space. -/
  normSq : space → ℝ
  /-- Energy functional on the reduced space. -/
  energy : space → ℝ
  /-- Exact coercive gap constant. -/
  gapConst : ℝ
  /-- Positivity of the gap constant. -/
  gap_pos : 0 < gapConst
  /-- Coercive lower bound on the reduced space. -/
  coercive : ∀ x : space, gapConst * normSq x ≤ energy x

/-- Canonical reduced coercive data on the explicit coercive sector. -/
def canonicalReducedCoerciveData : ReducedCoerciveData where
  space := CoerciveSector
  normSq := fun x => x.normSq
  energy := fun x => x.energy
  gapConst := 2
  gap_pos := by
    norm_num
  coercive := by
    intro x
    exact exact_coercive_gap_kappa_two_explicit x

/-- The canonical reduced coercive package has exact gap constant `2`. -/
theorem canonicalReducedCoerciveData_gap :
    canonicalReducedCoerciveData.gapConst = 2 := by
  rfl

/-- Explicit coercive inequality in the canonical reduced package. -/
theorem canonicalReducedCoerciveData_coercive (x : CoerciveSector) :
    canonicalReducedCoerciveData.gapConst * x.normSq ≤
      canonicalReducedCoerciveData.energy x := by
  exact canonicalReducedCoerciveData.coercive x

/-- First finite H1 bridge record: exact coercive data ready for spectral export. -/
structure H1BridgeRecord where
  /-- Exact reduced gap constant carried by the finite bridge. -/
  gapConst : ℝ
  /-- Identification of the exact finite gap with `2`. -/
  gap_eq_two : gapConst = 2
  /-- Exact coercive inequality on the explicit coercive sector. -/
  coercive_on_sector : ∀ x : CoerciveSector, gapConst * x.normSq ≤ x.energy

/-- Canonical finite H1 bridge extracted from the exact core. -/
def canonicalH1BridgeRecord : H1BridgeRecord where
  gapConst := 2
  gap_eq_two := rfl
  coercive_on_sector := by
    intro x
    exact exact_coercive_gap_kappa_two_explicit x

/-- The canonical H1 bridge has exact gap constant `2`. -/
theorem canonicalH1BridgeRecord_gap :
    canonicalH1BridgeRecord.gapConst = 2 := by
  rfl

/-- Explicit coercive inequality recorded by the canonical H1 bridge. -/
theorem canonicalH1BridgeRecord_coercive (x : CoerciveSector) :
    canonicalH1BridgeRecord.gapConst * x.normSq ≤ x.energy := by
  exact canonicalH1BridgeRecord.coercive_on_sector x

/-- The finite H1 bridge exists as an exact exported structure. -/
theorem finite_H1_bridge_exists : Nonempty H1BridgeRecord := by
  exact ⟨canonicalH1BridgeRecord⟩

/-- Publication-style summary: the finite core exports an exact reduced gap at `κ = 2`. -/
theorem finite_H1_bridge_summary :
    ∃ H : H1BridgeRecord,
      H.gapConst = 2 ∧
      ∀ x : CoerciveSector, H.gapConst * x.normSq ≤ x.energy := by
  refine ⟨canonicalH1BridgeRecord, ?_, ?_⟩
  · exact canonicalH1BridgeRecord_gap
  · intro x
    exact canonicalH1BridgeRecord_coercive x

/-- The finite bridge is nothing more and nothing less than the exact coercive sector
exported as an H1-type reduced object. -/
theorem finite_H1_bridge_is_exact_export :
    ∀ x : CoerciveSector, 2 * x.normSq ≤ x.energy := by
  intro x
  simpa [canonicalH1BridgeRecord_gap] using canonicalH1BridgeRecord_coercive x

/-- Canonical reduced coercive data also yields a nonempty reduced package. -/
theorem reduced_coercive_data_exists : Nonempty ReducedCoerciveData := by
  exact ⟨canonicalReducedCoerciveData⟩

/-- The reduced coercive package and the H1 bridge carry the same exact gap value. -/
theorem reduced_data_and_H1_bridge_share_gap :
    canonicalReducedCoerciveData.gapConst = canonicalH1BridgeRecord.gapConst := by
  rfl

end H1Bridge
end CouretUnification
