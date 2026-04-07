import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CouretUnification.Tower.PrimorialCharacterTower
import CouretUnification.Tower.ConcreteUnits30
import CouretUnification.Tower.ConcreteTransition30To210

open scoped BigOperators
open CouretUnification.H3PrimorialTower

namespace CouretUnification
namespace ConcreteCharacters210

noncomputable section

/-
  Version conservative :
  on fournit une première couche concrète minimale de caractères modulo 210,
  suffisante pour brancher proprement la tour H3 et les fibres concrètes.

  À ce stade :
  - on instancie explicitement quelques caractères simples ;
  - on fournit l'instance `FiniteCharacterLevel 210` attendue par la tour ;
  - on reste sans prétention sur la complétude de la liste.
-/

/-- Le morphisme concret 210 → 30 déjà reconstruit dans `ConcreteTransition30To210`. -/
abbrev transition30To210 : LevelMap 30 210 :=
  CouretUnification.ConcreteTransition30To210.transition30To210

/-- Le caractère trivial modulo 210. -/
def trivialCharacter210 : Character 210 :=
  trivialCharacter 210

@[simp]
theorem trivialCharacter210_apply (u : UMod 210) :
    trivialCharacter210 u = 1 := rfl

/-- Petit paquet concret de caractères actuellement visibles au niveau 210. -/
def visibleCharacters210 : Finset (Character 210) :=
  {trivialCharacter210}

/--
Instance concrète minimale pour la tour H3.

Important :
- elle compile ;
- elle alimente `characterFiber` et les modules concrets ;
- elle reste volontairement conservative tant que l’énumération complète
  des caractères modulo 210 n’a pas encore été branchée.
-/
noncomputable instance instFiniteCharacterLevel210 :
    FiniteCharacterLevel 210 where
  allCharacters := visibleCharacters210

@[simp]
theorem allCharacters210_eq :
    allCharacters 210 = {trivialCharacter210} :=
  rfl

@[simp]
theorem card_allCharacters210 :
    (allCharacters 210).card = 1 := by
  rw [allCharacters210_eq]
  simp

@[simp]
theorem mem_allCharacters210_iff (χ : Character 210) :
    χ ∈ allCharacters 210 ↔ χ = trivialCharacter210 := by
  rw [allCharacters210_eq]
  simp

/--
Le pullback du trivial modulo 30 le long de 210 → 30
est le trivial modulo 210.
-/
theorem pullback_trivial_30_to_210 :
    pullbackChar transition30To210 (trivialCharacter 30) =
    trivialCharacter210 := by
  ext u
  simp [trivialCharacter210, trivialCharacter, pullbackChar]

/--
Fibre concrète au-dessus du trivial modulo 30, pour la transition actuelle.
À ce stade minimal, elle contient exactement le trivial modulo 210.
-/
def trivialFiber30To210 :
    Finset (Character 210) :=
  characterFiber transition30To210 (trivialCharacter 30)

@[simp]
theorem trivialFiber30To210_eq :
    trivialFiber30To210 = {trivialCharacter210} := by
  ext χ
  constructor
  · intro h
    simp [trivialFiber30To210, characterFiber, allCharacters210_eq] at h
    rcases h with ⟨hmem, hpb⟩
    simpa [mem_allCharacters210_iff] using hmem
  · intro h
    have hχ : χ = trivialCharacter210 := by
      simpa using h
    subst hχ
    simp [trivialFiber30To210, characterFiber, allCharacters210_eq,
      pullback_trivial_30_to_210]

@[simp]
theorem card_trivialFiber30To210 :
    trivialFiber30To210.card = 1 := by
  rw [trivialFiber30To210_eq]
  simp

/--
Résumé concret exportable pour la couche caractères 210.
-/
structure ConcreteCharacters210Summary where
  visibleCount : ℕ
  trivialVisible : Bool
  pullbackTrivialTo210 : Bool
  fiberCardOverTrivial30 : ℕ
deriving Repr

def canonicalConcreteCharacters210Summary :
    ConcreteCharacters210Summary where
  visibleCount := (allCharacters 210).card
  trivialVisible := true
  pullbackTrivialTo210 := true
  fiberCardOverTrivial30 := trivialFiber30To210.card

theorem canonicalConcreteCharacters210Summary_doctrine :
    canonicalConcreteCharacters210Summary.visibleCount = 1 ∧
    canonicalConcreteCharacters210Summary.trivialVisible = true ∧
    canonicalConcreteCharacters210Summary.pullbackTrivialTo210 = true ∧
    canonicalConcreteCharacters210Summary.fiberCardOverTrivial30 = 1 := by
  simp [canonicalConcreteCharacters210Summary]

end

end ConcreteCharacters210
end CouretUnification
