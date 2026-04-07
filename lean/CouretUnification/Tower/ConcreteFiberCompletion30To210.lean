import CouretUnification.Tower.ConcreteFiberComparison30To210
import CouretUnification.Tower.ConcreteKernel210
import CouretUnification.Tower.ConcreteKernelLiftAction210

open CouretUnification.H3PrimorialTower

namespace CouretUnification
namespace ConcreteFiberCompletion30To210

noncomputable section

/-- Cardinal visible actuel de la fibre. -/
def visibleFiberCardinality : ℕ :=
  CouretUnification.ConcreteFiberComparison30To210.visibleFiberCardinality

/-- Cardinal cible (hérité du noyau). -/
def targetFiberCardinality : ℕ :=
  CouretUnification.ConcreteFiberComparison30To210.closedKernelCardinality

@[simp]
theorem visibleFiberCardinality_eq :
    visibleFiberCardinality = 1 := by
  simp [visibleFiberCardinality]

@[simp]
theorem targetFiberCardinality_eq :
    targetFiberCardinality = 6 := by
  simp [targetFiberCardinality]

/--
La fibre visible n’est pas encore complète.
-/
def fiberCompletionReached : Prop :=
  visibleFiberCardinality = targetFiberCardinality

theorem fiberCompletion_not_reached :
    ¬ fiberCompletionReached := by
  simp [fiberCompletionReached, visibleFiberCardinality_eq, targetFiberCardinality_eq]

/--
Écart restant à combler pour atteindre la complétion.
-/
def remainingFiberGap : ℕ :=
  targetFiberCardinality - visibleFiberCardinality

@[simp]
theorem remainingFiberGap_eq :
    remainingFiberGap = 5 := by
  simp [remainingFiberGap, visibleFiberCardinality_eq, targetFiberCardinality_eq]

/--
Statut de complétion de la fibre.
-/
structure ConcreteFiberCompletionSummary where
  visibleCardinality : ℕ
  targetCardinality : ℕ
  gap : ℕ
  kernelClosed : Bool
  orbitClosed : Bool
  completionReached : Bool
  status : TowerStepStatus
deriving Repr

def canonicalConcreteFiberCompletionSummary : ConcreteFiberCompletionSummary where
  visibleCardinality := visibleFiberCardinality
  targetCardinality := targetFiberCardinality
  gap := remainingFiberGap
  kernelClosed := true
  orbitClosed := true
  completionReached := false
  status := TowerStepStatus.scaffolded

theorem canonicalConcreteFiberCompletionSummary_doctrine :
    canonicalConcreteFiberCompletionSummary.visibleCardinality = 1 ∧
    canonicalConcreteFiberCompletionSummary.targetCardinality = 6 ∧
    canonicalConcreteFiberCompletionSummary.gap = 5 ∧
    canonicalConcreteFiberCompletionSummary.kernelClosed = true ∧
    canonicalConcreteFiberCompletionSummary.orbitClosed = true ∧
    canonicalConcreteFiberCompletionSummary.completionReached = false ∧
    canonicalConcreteFiberCompletionSummary.status = TowerStepStatus.scaffolded := by
  simp [
    canonicalConcreteFiberCompletionSummary,
    visibleFiberCardinality_eq,
    targetFiberCardinality_eq,
    remainingFiberGap_eq
  ]

/--
Version H7 : la complétion de la fibre est préparée mais non fermée.
-/
structure H7FiberCompletionRecord where
  bridgeStatus : BridgeStatus
  kernelClosed : Bool
  orbitClosed : Bool
  fiberCompletionClosed : Bool
  targetCardinality : ℕ
  currentStatus : WorkStatus
  proofStatus : TowerStepStatus
deriving Repr

def canonicalH7FiberCompletionRecord : H7FiberCompletionRecord where
  bridgeStatus := BridgeStatus.candidate
  kernelClosed := true
  orbitClosed := true
  fiberCompletionClosed := false
  targetCardinality := 6
  currentStatus := WorkStatus.ready
  proofStatus := TowerStepStatus.scaffolded

theorem canonicalH7FiberCompletionRecord_doctrine :
    canonicalH7FiberCompletionRecord.bridgeStatus = BridgeStatus.candidate ∧
    canonicalH7FiberCompletionRecord.kernelClosed = true ∧
    canonicalH7FiberCompletionRecord.orbitClosed = true ∧
    canonicalH7FiberCompletionRecord.fiberCompletionClosed = false ∧
    canonicalH7FiberCompletionRecord.targetCardinality = 6 ∧
    canonicalH7FiberCompletionRecord.currentStatus = WorkStatus.ready ∧
    canonicalH7FiberCompletionRecord.proofStatus = TowerStepStatus.scaffolded := by
  simp [canonicalH7FiberCompletionRecord]

end
end ConcreteFiberCompletion30To210
end CouretUnification
