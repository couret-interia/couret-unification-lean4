import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import CouretUnification.Tower.PrimorialCharacterTower
import CouretUnification.Tower.ConcreteCharacters210

open CouretUnification.H3PrimorialTower

namespace CouretUnification
namespace ConcreteCharacters210Family

noncomputable section

/--
Premier stade conservatif :
on repart de la couche visible actuelle.
-/
def visibleCharacterFamily210 : Finset (Character 210) :=
  CouretUnification.ConcreteCharacters210.visibleCharacters210

@[simp]
theorem visibleCharacterFamily210_eq :
    visibleCharacterFamily210 = {CouretUnification.ConcreteCharacters210.trivialCharacter210} := by
  rfl

@[simp]
theorem visibleCharacterFamily210_card :
    visibleCharacterFamily210.card = 1 := by
  simp [visibleCharacterFamily210_eq]

/--
Un caractère visible modulo 210 est, à ce stade, exactement le trivial.
-/
@[simp]
theorem mem_visibleCharacterFamily210_iff (χ : Character 210) :
    χ ∈ visibleCharacterFamily210 ↔
      χ = CouretUnification.ConcreteCharacters210.trivialCharacter210 := by
  simp [visibleCharacterFamily210_eq]

/--
Statut d’extension de la famille visible.
-/
structure ConcreteCharacters210FamilySummary where
  visibleCardinality : ℕ
  containsTrivial : Bool
  familyStatus : TowerStepStatus
  completeEnumeration : Bool
  targetCardinality : ℕ
deriving Repr

def canonicalConcreteCharacters210FamilySummary :
    ConcreteCharacters210FamilySummary where
  visibleCardinality := visibleCharacterFamily210.card
  containsTrivial := true
  familyStatus := TowerStepStatus.scaffolded
  completeEnumeration := false
  targetCardinality := 6

theorem canonicalConcreteCharacters210FamilySummary_doctrine :
    canonicalConcreteCharacters210FamilySummary.visibleCardinality = 1 ∧
    canonicalConcreteCharacters210FamilySummary.containsTrivial = true ∧
    canonicalConcreteCharacters210FamilySummary.familyStatus = TowerStepStatus.scaffolded ∧
    canonicalConcreteCharacters210FamilySummary.completeEnumeration = false ∧
    canonicalConcreteCharacters210FamilySummary.targetCardinality = 6 := by
  simp [
    canonicalConcreteCharacters210FamilySummary,
    visibleCharacterFamily210_card
  ]

/--
Version H7 :
la famille existe, mais son enrichissement reste ouvert.
-/
structure H7Characters210FamilyRecord where
  bridgeStatus : BridgeStatus
  visibleLayerReady : Bool
  currentVisibleCardinality : ℕ
  targetVisibleCardinality : ℕ
  familyStatus : TowerStepStatus
  workStatus : WorkStatus
  enumerationClosed : Bool
deriving Repr

def canonicalH7Characters210FamilyRecord :
    H7Characters210FamilyRecord where
  bridgeStatus := BridgeStatus.candidate
  visibleLayerReady := true
  currentVisibleCardinality := visibleCharacterFamily210.card
  targetVisibleCardinality := 6
  familyStatus := TowerStepStatus.scaffolded
  workStatus := WorkStatus.ready
  enumerationClosed := false

theorem canonicalH7Characters210FamilyRecord_doctrine :
    canonicalH7Characters210FamilyRecord.bridgeStatus = BridgeStatus.candidate ∧
    canonicalH7Characters210FamilyRecord.visibleLayerReady = true ∧
    canonicalH7Characters210FamilyRecord.currentVisibleCardinality = 1 ∧
    canonicalH7Characters210FamilyRecord.targetVisibleCardinality = 6 ∧
    canonicalH7Characters210FamilyRecord.familyStatus = TowerStepStatus.scaffolded ∧
    canonicalH7Characters210FamilyRecord.workStatus = WorkStatus.ready ∧
    canonicalH7Characters210FamilyRecord.enumerationClosed = false := by
  simp [
    canonicalH7Characters210FamilyRecord,
    visibleCharacterFamily210_card
  ]

end
end ConcreteCharacters210Family
end CouretUnification
