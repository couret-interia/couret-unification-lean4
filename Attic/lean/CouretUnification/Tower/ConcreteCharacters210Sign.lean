import CouretUnification.Tower.PrimorialCharacterTower
import CouretUnification.Tower.ConcreteCharacters210
import CouretUnification.Tower.ConcreteCharacters210Generators

open CouretUnification.H3PrimorialTower

namespace CouretUnification
namespace ConcreteCharacters210Sign

noncomputable section

/--
Premier slot pour un caractère "de signe" modulo 210.

À ce stade, il ne s'agit pas encore d'une construction explicite calculée
sur les unités modulo 210, mais d'un emplacement structuré pour le premier
caractère non trivial d'ordre 2 que l'on veut brancher dans la tour.
-/
structure SignCharacter210Slot where
  carrier : Character 210
  hasOrderTwo : Prop
  isNontrivial : Prop
  compatibleWithTransition30To210 : Prop

/--
Résumé exportable de la couche "sign".
-/
structure ConcreteCharacters210SignSummary where
  signSlotPresent : Bool
  explicitSignCharacterConstructed : Bool
  targetOrderTwo : Bool
  nontrivialityTarget : Bool
  status : TowerStepStatus
  workStatus : WorkStatus
deriving Repr

def canonicalConcreteCharacters210SignSummary :
    ConcreteCharacters210SignSummary where
  signSlotPresent := true
  explicitSignCharacterConstructed := false
  targetOrderTwo := true
  nontrivialityTarget := true
  status := TowerStepStatus.scaffolded
  workStatus := WorkStatus.ready

theorem canonicalConcreteCharacters210SignSummary_doctrine :
    canonicalConcreteCharacters210SignSummary.signSlotPresent = true ∧
    canonicalConcreteCharacters210SignSummary.explicitSignCharacterConstructed = false ∧
    canonicalConcreteCharacters210SignSummary.targetOrderTwo = true ∧
    canonicalConcreteCharacters210SignSummary.nontrivialityTarget = true ∧
    canonicalConcreteCharacters210SignSummary.status = TowerStepStatus.scaffolded ∧
    canonicalConcreteCharacters210SignSummary.workStatus = WorkStatus.ready := by
  simp [canonicalConcreteCharacters210SignSummary]

/--
Version H7 : la couche "sign" est prête à être fermée, mais pas encore prouvée.
-/
structure H7Characters210SignRecord where
  bridgeStatus : BridgeStatus
  signLayerReady : Bool
  explicitCharacterAvailable : Bool
  orderTwoVerified : Bool
  nontrivialityVerified : Bool
  status : TowerStepStatus
  workStatus : WorkStatus
deriving Repr

def canonicalH7Characters210SignRecord :
    H7Characters210SignRecord where
  bridgeStatus := BridgeStatus.candidate
  signLayerReady := true
  explicitCharacterAvailable := false
  orderTwoVerified := false
  nontrivialityVerified := false
  status := TowerStepStatus.scaffolded
  workStatus := WorkStatus.ready

theorem canonicalH7Characters210SignRecord_doctrine :
    canonicalH7Characters210SignRecord.bridgeStatus = BridgeStatus.candidate ∧
    canonicalH7Characters210SignRecord.signLayerReady = true ∧
    canonicalH7Characters210SignRecord.explicitCharacterAvailable = false ∧
    canonicalH7Characters210SignRecord.orderTwoVerified = false ∧
    canonicalH7Characters210SignRecord.nontrivialityVerified = false ∧
    canonicalH7Characters210SignRecord.status = TowerStepStatus.scaffolded ∧
    canonicalH7Characters210SignRecord.workStatus = WorkStatus.ready := by
  simp [canonicalH7Characters210SignRecord]

end
end ConcreteCharacters210Sign
end CouretUnification
