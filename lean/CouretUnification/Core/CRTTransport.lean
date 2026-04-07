import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace CouretUnification.Core

def transportedParsevalMass (q : Nat) : Nat :=
  3 * Nat.totient q

lemma transportedParsevalMass_30 :
    transportedParsevalMass 30 = 24 := by
  native_decide

lemma transportedParsevalMass_210 :
    transportedParsevalMass 210 = 144 := by
  native_decide

end CouretUnification.Core
