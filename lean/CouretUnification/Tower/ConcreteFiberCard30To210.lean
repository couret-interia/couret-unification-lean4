import CouretUnification.Tower.ConcreteKernel210
import CouretUnification.Tower.ConcreteCharacters210

open CouretUnification.H3PrimorialTower
open CouretUnification.ConcreteTransition30To210
open CouretUnification.ConcreteKernel210
open CouretUnification.ConcreteCharacters210

namespace CouretUnification
namespace ConcreteFiberCard30To210

noncomputable section

def trivialFiberCardinality : ℕ :=
  trivialFiber30To210.card

theorem trivialFiberCardinality_eq_one :
    trivialFiberCardinality = 1 := by
  simp [trivialFiberCardinality]

/--
Doctrinal target for the future full character tower:
once the fiber is fully populated, its cardinal should match the kernel cardinal.
-/
def trivialFiberHasTargetCardinality : Prop :=
  trivialFiberCardinality = 6

theorem kernel_has_target_cardinality :
    kernelTransition30To210Finset.card = 6 := by
  simpa using ConcreteKernel210.kernelTransition30To210Finset_card

structure ConcreteFiberCardSummary where
  currentFiberCardinality : ℕ
  targetFiberCardinality : ℕ
  currentStatus : TowerStepStatus
  kernelCardinalityClosed : Bool
  fiberCardinalityClosed : Bool
deriving Repr

def canonicalConcreteFiberCardSummary : ConcreteFiberCardSummary where
  currentFiberCardinality := trivialFiberCardinality
  targetFiberCardinality := 6
  currentStatus := TowerStepStatus.scaffolded
  kernelCardinalityClosed := true
  fiberCardinalityClosed := false

theorem canonicalConcreteFiberCardSummary_doctrine :
    canonicalConcreteFiberCardSummary.currentFiberCardinality = 1 ∧
    canonicalConcreteFiberCardSummary.targetFiberCardinality = 6 ∧
    canonicalConcreteFiberCardSummary.currentStatus = TowerStepStatus.scaffolded ∧
    canonicalConcreteFiberCardSummary.kernelCardinalityClosed = true ∧
    canonicalConcreteFiberCardSummary.fiberCardinalityClosed = false := by
  simp [canonicalConcreteFiberCardSummary, trivialFiberCardinality]

end
end ConcreteFiberCard30To210
end CouretUnification
