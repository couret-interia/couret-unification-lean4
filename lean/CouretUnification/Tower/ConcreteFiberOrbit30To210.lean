import CouretUnification.Tower.PrimorialCharacterTower
import CouretUnification.Tower.ConcreteCharacters210
import CouretUnification.Tower.ConcreteCharacters210Lift
import CouretUnification.Tower.ConcreteFiberCard30To210
import CouretUnification.Tower.ConcreteKernelLiftAction210

open CouretUnification.H3PrimorialTower
open CouretUnification.ConcreteCharacters210
open CouretUnification.ConcreteCharacters210Lift
open CouretUnification.ConcreteFiberCard30To210
open CouretUnification.ConcreteKernelLiftAction210

namespace CouretUnification
namespace ConcreteFiberOrbit30To210

noncomputable section

/-- Le lift trivial redonne bien le caractère trivial modulo 210. -/
@[simp]
theorem liftToCharacter_trivialLiftCandidate :
    liftToCharacter trivialLiftCandidate = trivialCharacter210 := rfl

/--
Projection de l’orbite visible du lift trivial vers les caractères.
Dans l’état actuel, cette image est le singleton du caractère trivial modulo 210.
-/
def trivialLiftOrbitCharacterImage : Finset (Character 210) :=
  trivialLiftVisibleOrbit.image liftToCharacter

@[simp]
theorem trivialLiftOrbitCharacterImage_eq :
    trivialLiftOrbitCharacterImage = ({trivialCharacter210} : Finset (Character 210)) := by
  ext χ
  simp [trivialLiftOrbitCharacterImage, trivialLiftVisibleOrbit, kernelLiftOrbit]

@[simp]
theorem trivialLiftOrbitCharacterImage_card :
    trivialLiftOrbitCharacterImage.card = 1 := by
  simp [trivialLiftOrbitCharacterImage_eq]

/--
Cardinal courant de l’orbite visible au niveau des lifts.
-/
def trivialLiftOrbitCardinality : ℕ :=
  trivialLiftVisibleOrbit.card

@[simp]
theorem trivialLiftOrbitCardinality_eq_one :
    trivialLiftOrbitCardinality = 1 := by
  simp [trivialLiftOrbitCardinality, trivialLiftVisibleOrbit, kernelLiftOrbit]

/--
Comparaison conservative entre l’orbite visible actuelle et la fibre visible actuelle.
À ce stade, les deux cardinaux valent `1`.
-/
theorem trivialLiftOrbitCardinality_matches_visibleFiber :
    trivialLiftOrbitCardinality = trivialFiberCardinality := by
  simp [trivialLiftOrbitCardinality, trivialFiberCardinality, trivialLiftVisibleOrbit, kernelLiftOrbit]

/--
Cible doctrinale future : une fois la tour des lifts pleinement déployée,
le cardinal de l’orbite visible devrait refléter la cible `6`.
-/
def trivialLiftOrbitHasTargetCardinality : Prop :=
  trivialLiftOrbitCardinality = 6

/--
Résumé concret exportable pour la couche "fiber orbit 30 -> 210".
-/
structure ConcreteFiberOrbitSummary where
  currentOrbitCardinality : ℕ
  currentVisibleFiberCardinality : ℕ
  targetCardinality : ℕ
  projectionCompatible : Bool
  currentStatus : TowerStepStatus
  theoremAvailable : Bool
deriving Repr

def canonicalConcreteFiberOrbitSummary : ConcreteFiberOrbitSummary where
  currentOrbitCardinality := trivialLiftOrbitCardinality
  currentVisibleFiberCardinality := trivialFiberCardinality
  targetCardinality := 6
  projectionCompatible := true
  currentStatus := TowerStepStatus.scaffolded
  theoremAvailable := false

theorem canonicalConcreteFiberOrbitSummary_doctrine :
    canonicalConcreteFiberOrbitSummary.currentOrbitCardinality = 1 ∧
    canonicalConcreteFiberOrbitSummary.currentVisibleFiberCardinality = 1 ∧
    canonicalConcreteFiberOrbitSummary.targetCardinality = 6 ∧
    canonicalConcreteFiberOrbitSummary.projectionCompatible = true ∧
    canonicalConcreteFiberOrbitSummary.currentStatus = TowerStepStatus.scaffolded ∧
    canonicalConcreteFiberOrbitSummary.theoremAvailable = false := by
  simp [
    canonicalConcreteFiberOrbitSummary,
    trivialLiftOrbitCardinality,
    trivialFiberCardinality,
    trivialLiftVisibleOrbit,
    kernelLiftOrbit
  ]

/--
Version H7 : l’orbite de lifts est branchée, la projection est compatible,
mais l’égalité entre cardinal d’orbite et cardinal cible `6` reste ouverte.
-/
structure H7FiberOrbitWorkRecord where
  bridgeStatus : BridgeStatus
  liftOrbitStatus : WorkStatus
  fiberStatus : WorkStatus
  comparisonStatus : WorkStatus
  proofStatus : TowerStepStatus
  targetCardinality : ℕ
  theoremAvailable : Bool
deriving Repr

def canonicalH7FiberOrbitWorkRecord : H7FiberOrbitWorkRecord where
  bridgeStatus := BridgeStatus.candidate
  liftOrbitStatus := WorkStatus.done
  fiberStatus := WorkStatus.done
  comparisonStatus := WorkStatus.ready
  proofStatus := TowerStepStatus.scaffolded
  targetCardinality := 6
  theoremAvailable := false

theorem canonicalH7FiberOrbitWorkRecord_doctrine :
    canonicalH7FiberOrbitWorkRecord.bridgeStatus = BridgeStatus.candidate ∧
    canonicalH7FiberOrbitWorkRecord.liftOrbitStatus = WorkStatus.done ∧
    canonicalH7FiberOrbitWorkRecord.fiberStatus = WorkStatus.done ∧
    canonicalH7FiberOrbitWorkRecord.comparisonStatus = WorkStatus.ready ∧
    canonicalH7FiberOrbitWorkRecord.proofStatus = TowerStepStatus.scaffolded ∧
    canonicalH7FiberOrbitWorkRecord.targetCardinality = 6 ∧
    canonicalH7FiberOrbitWorkRecord.theoremAvailable = false := by
  simp [canonicalH7FiberOrbitWorkRecord]

end
end ConcreteFiberOrbit30To210
end CouretUnification
