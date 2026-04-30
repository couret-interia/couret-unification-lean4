/-
  Couret-Unification — v35.9.0
  AnalyticHorizon/Det2Obligations.lean

  Objet : OBLIGATIONS TYPÉES POUR Det2Transport.

  Statut     : Frozen-eligible (0 sorry, 0 axiome local, structures uniquement)
  Layer      : AnalyticHorizon
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0

  Renommage doctrinal v35.9 : A1_num / A2_den / A3_bound / A4_critical.

  Pour Bernard.
-/

namespace CouretUnification.AnalyticHorizon

/- ═══════════════════════════════════════════════════════════════════════════
   LES QUATRE OBLIGATIONS Det2
   ═══════════════════════════════════════════════════════════════════════════ -/

structure Det2Obligations where
  /-- A1_num : le numérateur du défaut régularisé est borné. -/
  numeratorBounded         : Prop
  /-- A2_den : le dénominateur du défaut régularisé est borné en valeur
      absolue PAR EN BAS, sur la ligne critique, par une constante > 0. -/
  denominatorBoundedBelow  : Prop
  /-- A3_bound : argument de compacité (Hille-Tamarkin ou convergence dominée). -/
  compactnessArgument      : Prop
  /-- A4_critical : contrôle uniforme du défaut régularisé sur la ligne
      critique Re(s) = 1/2 — le verrou doctrinal historique du programme. -/
  criticalLineControl      : Prop

def Det2Admissible (o : Det2Obligations) : Prop :=
  o.numeratorBounded
  ∧ o.denominatorBoundedBelow
  ∧ o.compactnessArgument
  ∧ o.criticalLineControl

/- ═══════════════════════════════════════════════════════════════════════════
   THÉORÈMES DE PROJECTION
   ═══════════════════════════════════════════════════════════════════════════ -/

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

/- ═══════════════════════════════════════════════════════════════════════════
   GATE FCI
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Spécification de la conclusion de Det2Transport (à instancier dans Active). -/
opaque Det2TransportConclusion : Prop

/-- Forme du théorème conditionnel — pas prouvé ici. -/
def Det2TransportSignature : Prop :=
  ∀ o : Det2Obligations, Det2Admissible o → Det2TransportConclusion

theorem no_det2_claim_without_obligations
    (o : Det2Obligations) (h : ¬ Det2Admissible o) :
    ¬ (Det2Admissible o ∧ Det2TransportConclusion) := by
  intro ⟨ha, _⟩
  exact h ha

end CouretUnification.AnalyticHorizon
