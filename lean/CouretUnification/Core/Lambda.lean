import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable def lambda8 : ℝ := 1 / Real.sqrt 7

lemma lambda8_def : lambda8 = 1 / Real.sqrt 7 := by
  rfl

lemma lambda8_sq : lambda8 ^ 2 = 1 / 7 := by
  have h7 : (0 : ℝ) ≤ 7 := by norm_num
  rw [lambda8_def]
  have hs : Real.sqrt 7 * Real.sqrt 7 = 7 := by
    nlinarith [Real.sq_sqrt h7]
  field_simp [hs]
  norm_num

end CouretUnification.Core