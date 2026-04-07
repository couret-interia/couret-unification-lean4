import CouretUnification.Core.SpectralProfile
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace CouretUnification.Core

def parsevalMass : Nat := TCParsevalMass

lemma parsevalMass_eq_24 : parsevalMass = 24 := by
  simpa [parsevalMass] using TCParsevalMass_eq

example : 2 * 9 + 6 * 1 = 24 := by
  norm_num

end CouretUnification.Core