import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Defs

namespace CouretUnification.Core

abbrev Residue := ZMod 30
abbrev Idx := Fin 8

def admissibleResidues : List Nat := [1, 7, 11, 13, 17, 19, 23, 29]

def residueVal : Idx → Nat
| ⟨0, _⟩ => 1
| ⟨1, _⟩ => 7
| ⟨2, _⟩ => 11
| ⟨3, _⟩ => 13
| ⟨4, _⟩ => 17
| ⟨5, _⟩ => 19
| ⟨6, _⟩ => 23
| ⟨7, _⟩ => 29

lemma residueVal_mem (i : Idx) : residueVal i ∈ admissibleResidues := by
  fin_cases i <;> decide

example : admissibleResidues.length = 8 := by
  decide

end CouretUnification.Core