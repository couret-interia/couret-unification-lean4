import CouretUnification.Logic.ExplicitFormula.TraceObject

namespace CouretUnification.Logic.ExplicitFormula

/--
Abstract archimedean kernel.

In Frozen, this is not yet the digamma kernel.
It is a parametrized kernel with a growth obligation.
-/
structure ArchimedeanKernel where
  K : ℝ → ℂ
  logarithmicGrowth : Prop

/--
Archimedean side as typed data.

The real digamma/Gamma instantiation belongs to Active,
not to Frozen.
-/
structure ArchimedeanSide where
  kernel : ArchimedeanKernel
  side : FormulaSide
  integrabilityObligation : Prop

end CouretUnification.Logic.ExplicitFormula
