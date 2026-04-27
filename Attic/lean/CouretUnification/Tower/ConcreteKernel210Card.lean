import CouretUnification.Tower.ConcreteKernel210

namespace CouretUnification
namespace ConcreteKernel210Card

open CouretUnification.ConcreteKernel210

structure ConcreteKernel210CardSummary where
  kernelCardinality : ℕ
  expectedCardinality : ℕ
  proofClosed : Bool
deriving Repr

def canonicalConcreteKernel210CardSummary :
    ConcreteKernel210CardSummary where
  kernelCardinality := kernelTransition30To210Finset.card
  expectedCardinality := 6
  proofClosed := true

theorem canonicalConcreteKernel210CardSummary_doctrine :
    canonicalConcreteKernel210CardSummary.kernelCardinality = 6 ∧
    canonicalConcreteKernel210CardSummary.expectedCardinality = 6 ∧
    canonicalConcreteKernel210CardSummary.proofClosed = true := by
  constructor
  · simpa [canonicalConcreteKernel210CardSummary] using
      kernelTransition30To210Finset_card
  constructor
  · rfl
  · rfl

end ConcreteKernel210Card
end CouretUnification
