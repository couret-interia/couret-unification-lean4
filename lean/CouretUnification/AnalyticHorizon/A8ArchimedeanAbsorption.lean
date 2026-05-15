import Mathlib.Data.Finset.Powerset
import CouretUnification.Logic.ExplicitFormula.TraceObject

namespace CouretUnification.AnalyticHorizon

open CouretUnification.Logic.ExplicitFormula

/-- The six active vertices after removing the reflection pole 29. -/
def U30A8 : Finset ℕ :=
  [7, 11, 13, 17, 19, 23].toFinset

/-- The six reflection edges attached to the pole 29. -/
def ReflectionEdges : Finset (ℕ × ℕ) :=
  U30A8.image fun x => (x, 29)

/-- Cardinality of the reflection shell. -/
theorem reflectionEdges_card_eq_6 :
    ReflectionEdges.card = 6 := by
  native_decide

/-- Raw number of edges in K₇. -/
def M4_raw : ℕ := Nat.choose 7 2

/-- Effective number of edges in K₆. -/
def M4_eff : ℕ := Nat.choose 6 2

/-- A8 residue. -/
def R_A8 : ℕ := M4_raw - M4_eff

/-- The finite combinatorial residue is six. -/
theorem R_A8_eq_6 : R_A8 = 6 := by
  native_decide

/--
Typed correction attached to the A8 residue.

No Sonine transport is proved here.
No KMS origin is proved here.
No RH consequence is exported.
-/
structure A8ArchimedeanCorrection where
  correctionSide : FormulaSide
  residueCard : ℕ
  residueCard_eq_six : residueCard = 6
  no_rh_claim : True

end CouretUnification.AnalyticHorizon
