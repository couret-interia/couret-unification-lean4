import CouretUnification.Core.Mod30
import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace CouretUnification.Core

abbrev CharIdx := Fin 8
abbrev Character30 := Idx → ℂ

/--
Coordonnées CRT des 8 résidus actifs, dans l'ordre
[1, 7, 11, 13, 17, 19, 23, 29].

On utilise ici une identification finie documentaire avec `C₂ × C₄`.
-/
def residueCoord : Idx → Fin 2 × Fin 4
  | ⟨0, _⟩ => (0, 0)  -- 1
  | ⟨1, _⟩ => (0, 1)  -- 7
  | ⟨2, _⟩ => (1, 2)  -- 11
  | ⟨3, _⟩ => (0, 3)  -- 13
  | ⟨4, _⟩ => (1, 3)  -- 17
  | ⟨5, _⟩ => (0, 2)  -- 19
  | ⟨6, _⟩ => (1, 1)  -- 23
  | ⟨7, _⟩ => (1, 0)  -- 29

/--
Ordre documentaire des caractères.

On le choisit pour que le triplet distingué `T_C = {1,11,29}`
ait le spectre brut historique
`[3,1,1,1,3,1,-1,-1]`,
et donc le profil quadratique historique
`[9,1,1,1,9,1,1,1]`.
-/
def charCoord : CharIdx → Fin 2 × Fin 4
  | ⟨0, _⟩ => (0, 0)
  | ⟨1, _⟩ => (0, 1)
  | ⟨2, _⟩ => (0, 3)
  | ⟨3, _⟩ => (1, 1)
  | ⟨4, _⟩ => (0, 2)
  | ⟨5, _⟩ => (1, 3)
  | ⟨6, _⟩ => (1, 0)
  | ⟨7, _⟩ => (1, 2)

/-- Facteur C₂ du caractère. -/
def c2Phase : Fin 2 → Fin 2 → ℂ
  | ⟨0, _⟩, _        => 1
  | ⟨1, _⟩, ⟨0, _⟩   => 1
  | ⟨1, _⟩, ⟨1, _⟩   => -1

/-- Facteur C₄ du caractère. -/
def c4Phase (b k : Fin 4) : ℂ :=
  Complex.I ^ (b.1 * k.1)

/-- Évaluation du caractère d'indice χ sur le résidu actif g. -/
def characterEval (χ : CharIdx) (g : Idx) : ℂ :=
  let (u, b) := charCoord χ
  let (ε, k) := residueCoord g
  c2Phase u ε * c4Phase b k

/-- Le caractère χ comme fonction `Idx → ℂ`. -/
def character (χ : CharIdx) : Character30 :=
  fun g => characterEval χ g

/-- Liste ordonnée documentaire des 8 caractères. -/
def documentaryCharacters : List CharIdx :=
  List.finRange 8

lemma documentaryCharacters_length :
    documentaryCharacters.length = 8 := by
  native_decide

/-- Le caractère trivial est l'indice 0 dans cette convention. -/
def trivialCharacter : Character30 := character 0

lemma trivialCharacter_eval (g : Idx) :
    trivialCharacter g = 1 := by
  fin_cases g <;>
    norm_num [trivialCharacter, character, characterEval, charCoord, residueCoord, c2Phase, c4Phase]

/-
À ce stade, `Characters30.lean` ne prétend pas encore :
- prouver l'orthogonalité complète,
- définir la DFT finie générale,
- fermer `hasIntegralSpectrum`.

Il gèle seulement les coordonnées et l'ordre documentaire.
-/

end CouretUnification.Core