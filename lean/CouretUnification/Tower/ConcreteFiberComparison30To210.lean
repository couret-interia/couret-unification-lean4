import CouretUnification.Tower.ConcreteFiberCard30To210
import CouretUnification.Tower.ConcreteFiberOrbit30To210
import CouretUnification.Tower.ConcreteKernel210
import CouretUnification.Tower.ConcreteKernelLiftAction210

open CouretUnification.H3PrimorialTower

namespace CouretUnification
namespace ConcreteFiberComparison30To210

noncomputable section

/-- Cardinal visible actuel de la fibre au-dessus du trivial modulo 30. -/
def visibleFiberCardinality : ℕ :=
  CouretUnification.ConcreteFiberCard30To210.trivialFiberCardinality

/-- Cardinal fermé du noyau de la transition `210 → 30`. -/
def closedKernelCardinality : ℕ :=
  CouretUnification.ConcreteKernel210.kernelTransition30To210Finset.card

@[simp]
theorem visibleFiberCardinality_eq :
    visibleFiberCardinality = 1 := by
  unfold visibleFiberCardinality
  exact CouretUnification.ConcreteFiberCard30To210.trivialFiberCardinality_eq_one

@[simp]
theorem closedKernelCardinality_eq :
    closedKernelCardinality = 6 := by
  simpa [closedKernelCardinality] using
    CouretUnification.ConcreteKernel210.kernelTransition30To210Finset_card

/--
Écart actuel entre la fibre visible et la cible fermée.
Dans l’état présent, la fibre visible n’est pas encore saturée.
-/
def fiberKernelGap : ℕ :=
  closedKernelCardinality - visibleFiberCardinality

@[simp]
theorem fiberKernelGap_eq :
    fiberKernelGap = 5 := by
  simp [fiberKernelGap, visibleFiberCardinality_eq, closedKernelCardinality_eq]

/--
La comparaison doctrinale attendue à terme :
la fibre complète devra avoir même cardinal que le noyau.
-/
def targetFiberKernelAgreement : Prop :=
  visibleFiberCardinality = closedKernelCardinality

theorem targetFiberKernelAgreement_currently_false :
    ¬ targetFiberKernelAgreement := by
  simp [targetFiberKernelAgreement, visibleFiberCardinality_eq, closedKernelCardinality_eq]

/-- Cardinal visible actuel de l’orbite du lift trivial. -/
def visibleOrbitCardinality : ℕ :=
  CouretUnification.ConcreteKernelLiftAction210.trivialLiftVisibleOrbit.card

@[simp]
theorem visibleOrbitCardinality_eq :
    visibleOrbitCardinality = 1 := by
  simp [visibleOrbitCardinality]

/--
Accord visible fibre/orbite : fermé dans le modèle minimal courant.
-/
def visibleFiberOrbitAgreement : Prop :=
  visibleFiberCardinality = visibleOrbitCardinality

theorem visibleFiberOrbitAgreement_true :
    visibleFiberOrbitAgreement := by
  simp [
    visibleFiberOrbitAgreement,
    visibleFiberCardinality_eq,
    visibleOrbitCardinality_eq
  ]

/-- Résumé exportable de la comparaison fibre/noyau/orbite. -/
structure ConcreteFiberComparisonSummary where
  visibleFiberCardinality : ℕ
  visibleOrbitCardinality : ℕ
  closedKernelCardinality : ℕ
  fiberOrbitAgreement : Bool
  fiberKernelAgreement : Bool
  gapToTarget : ℕ
  currentStatus : TowerStepStatus
deriving Repr

def canonicalConcreteFiberComparisonSummary : ConcreteFiberComparisonSummary where
  visibleFiberCardinality := visibleFiberCardinality
  visibleOrbitCardinality := visibleOrbitCardinality
  closedKernelCardinality := closedKernelCardinality
  fiberOrbitAgreement := true
  fiberKernelAgreement := false
  gapToTarget := fiberKernelGap
  currentStatus := TowerStepStatus.scaffolded

theorem canonicalConcreteFiberComparisonSummary_doctrine :
    canonicalConcreteFiberComparisonSummary.visibleFiberCardinality = 1 ∧
    canonicalConcreteFiberComparisonSummary.visibleOrbitCardinality = 1 ∧
    canonicalConcreteFiberComparisonSummary.closedKernelCardinality = 6 ∧
    canonicalConcreteFiberComparisonSummary.fiberOrbitAgreement = true ∧
    canonicalConcreteFiberComparisonSummary.fiberKernelAgreement = false ∧
    canonicalConcreteFiberComparisonSummary.gapToTarget = 5 ∧
    canonicalConcreteFiberComparisonSummary.currentStatus = TowerStepStatus.scaffolded := by
  simp [
    canonicalConcreteFiberComparisonSummary,
    visibleFiberCardinality_eq,
    visibleOrbitCardinality_eq,
    closedKernelCardinality_eq,
    fiberKernelGap_eq
  ]

/--
Version H7 : la comparaison est structurée,
mais l’égalité complète fibre = noyau reste ouverte.
-/
structure H7FiberComparisonRecord where
  bridgeStatus : BridgeStatus
  visibleFiberClosed : Bool
  visibleOrbitClosed : Bool
  kernelClosed : Bool
  fullComparisonClosed : Bool
  targetCardinality : ℕ
  currentStatus : WorkStatus
  proofStatus : TowerStepStatus
deriving Repr

def canonicalH7FiberComparisonRecord : H7FiberComparisonRecord where
  bridgeStatus := BridgeStatus.candidate
  visibleFiberClosed := true
  visibleOrbitClosed := true
  kernelClosed := true
  fullComparisonClosed := false
  targetCardinality := 6
  currentStatus := WorkStatus.ready
  proofStatus := TowerStepStatus.scaffolded

theorem canonicalH7FiberComparisonRecord_doctrine :
    canonicalH7FiberComparisonRecord.bridgeStatus = BridgeStatus.candidate ∧
    canonicalH7FiberComparisonRecord.visibleFiberClosed = true ∧
    canonicalH7FiberComparisonRecord.visibleOrbitClosed = true ∧
    canonicalH7FiberComparisonRecord.kernelClosed = true ∧
    canonicalH7FiberComparisonRecord.fullComparisonClosed = false ∧
    canonicalH7FiberComparisonRecord.targetCardinality = 6 ∧
    canonicalH7FiberComparisonRecord.currentStatus = WorkStatus.ready ∧
    canonicalH7FiberComparisonRecord.proofStatus = TowerStepStatus.scaffolded := by
  simp [canonicalH7FiberComparisonRecord]

end
end ConcreteFiberComparison30To210
end CouretUnification
