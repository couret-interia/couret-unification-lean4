/-
  Couret-Unification — v35.9.1
  AnalyticHorizon/Det2Obligations.lean

  Objet : OBLIGATIONS TYPÉES pour Det2Transport.

  Statut     : Frozen-eligible (0 sorry, 0 axiome local)
  Renommage  : A1_num / A2_den / A3_bound / A4_critical.

  Pour Bernard.
-/

namespace CouretUnification.AnalyticHorizon

structure Det2Obligations where
  numeratorBounded         : Prop
  denominatorBoundedBelow  : Prop
  compactnessArgument      : Prop
  criticalLineControl      : Prop

def Det2Admissible (o : Det2Obligations) : Prop :=
  o.numeratorBounded
  ∧ o.denominatorBoundedBelow
  ∧ o.compactnessArgument
  ∧ o.criticalLineControl

theorem det2_admissible_implies_A1_num
    (o : Det2Obligations) (h : Det2Admissible o) :
    o.numeratorBounded := h.1

theorem det2_admissible_implies_A2_den
    (o : Det2Obligations) (h : Det2Admissible o) :
    o.denominatorBoundedBelow := h.2.1

theorem det2_admissible_implies_A3_bound
    (o : Det2Obligations) (h : Det2Admissible o) :
    o.compactnessArgument := h.2.2.1

theorem det2_admissible_implies_A4_critical
    (o : Det2Obligations) (h : Det2Admissible o) :
    o.criticalLineControl := h.2.2.2

/-- Spécification de la conclusion (à instancier en Active). -/
opaque Det2TransportConclusion : Prop

def Det2TransportSignature : Prop :=
  ∀ o : Det2Obligations, Det2Admissible o → Det2TransportConclusion

theorem no_det2_claim_without_obligations
    (o : Det2Obligations) (h : ¬ Det2Admissible o) :
    ¬ (Det2Admissible o ∧ Det2TransportConclusion) := by
  intro ⟨ha, _⟩
  exact h ha

end CouretUnification.AnalyticHorizon
