import CouretUnification.Core.CRTTransport
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable def invariantE (q : Nat) : ℚ :=
  (transportedParsevalMass q : ℚ) / (Nat.totient q : ℚ)

lemma invariantE_30 : invariantE 30 = 3 := by
  have hphi : Nat.totient 30 = 8 := by native_decide
  rw [invariantE, transportedParsevalMass_30, hphi]
  norm_num

lemma invariantE_210 : invariantE 210 = 3 := by
  have hphi : Nat.totient 210 = 48 := by native_decide
  rw [invariantE, transportedParsevalMass_210, hphi]
  norm_num

end CouretUnification.Core