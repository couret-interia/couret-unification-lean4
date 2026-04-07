import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace CouretUnification.Core

def sgResidues : List Nat := [11, 23, 29]

lemma sgResidues_length : sgResidues.length = 3 := by
  decide

lemma sg_11_mem : 11 ∈ sgResidues := by decide
lemma sg_23_mem : 23 ∈ sgResidues := by decide
lemma sg_29_mem : 29 ∈ sgResidues := by decide

end CouretUnification.Core