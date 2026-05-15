/-
  CouretUnification.AnalyticHorizon.Det2Obligations
  ════════════════════════════════════════════════════════════════════
  Obligations typées pour le transport det₂.

  Objet
  -----
  Ce fichier ne prouve pas le transport déterminantiel. Il isole les
  quatre obligations minimales A1–A4 nécessaires avant toute conclusion
  de type `Det2Transport`.

  Les obligations sont conservées comme champs propositionnels explicites :

    • A1_num      : bornitude du numérateur ;
    • A2_den      : minoration du dénominateur ;
    • A3_bound    : argument de compacité / contrôle global ;
    • A4_critical : contrôle sur la ligne critique.

  Rôle
  ----
  `Det2Admissible` regroupe ces quatre obligations. Les lemmes suivants
  ne font que projeter les composantes A1–A4 depuis une preuve
  d'admissibilité complète.

  Garde-fous
  ----------
    • aucune identité det₂ n'est prouvée ici ;
    • aucune conclusion analytique n'est exportée sans obligations ;
    • aucune fermeture de formule explicite n'est revendiquée ;
    • aucune conséquence RH ou Hilbert–Pólya n'est affirmée.

  Statut
  ------
  Frozen-eligible :
    0 sorry,
    0 axiome local.

  Héritage : v35.9.1.
  Renommage : A1_num / A2_den / A3_bound / A4_critical.

  Pour Bernard.
-/

namespace CouretUnification.AnalyticHorizon

/-- Les quatre obligations typées nécessaires au transport det₂. -/
structure Det2Obligations where
  /-- A1_num : le numérateur est borné. -/
  numeratorBounded         : Prop
  /-- A2_den : le dénominateur est borné inférieurement. -/
  denominatorBoundedBelow  : Prop
  /-- A3_bound : l'argument de compacité / contrôle global est disponible. -/
  compactnessArgument      : Prop
  /-- A4_critical : le contrôle sur la ligne critique est disponible. -/
  criticalLineControl      : Prop

/-- Admissibilité det₂ : les quatre obligations A1–A4 sont satisfaites. -/
def Det2Admissible (o : Det2Obligations) : Prop :=
  o.numeratorBounded
  ∧ o.denominatorBoundedBelow
  ∧ o.compactnessArgument
  ∧ o.criticalLineControl

/-- Projection A1_num depuis une preuve d'admissibilité det₂. -/
theorem det2_admissible_implies_A1_num
    (o : Det2Obligations) (h : Det2Admissible o) :
    o.numeratorBounded := h.1

/-- Projection A2_den depuis une preuve d'admissibilité det₂. -/
theorem det2_admissible_implies_A2_den
    (o : Det2Obligations) (h : Det2Admissible o) :
    o.denominatorBoundedBelow := h.2.1

/-- Projection A3_bound depuis une preuve d'admissibilité det₂. -/
theorem det2_admissible_implies_A3_bound
    (o : Det2Obligations) (h : Det2Admissible o) :
    o.compactnessArgument := h.2.2.1

/-- Projection A4_critical depuis une preuve d'admissibilité det₂. -/
theorem det2_admissible_implies_A4_critical
    (o : Det2Obligations) (h : Det2Admissible o) :
    o.criticalLineControl := h.2.2.2

/-- Spécification opaque de la conclusion du transport det₂.

    Cette conclusion devra être instanciée dans la couche Active. Elle est
    volontairement opaque ici : ce fichier définit la forme de l'obligation,
    non son contenu analytique final. -/
opaque Det2TransportConclusion : Prop

/-- Signature attendue du transport det₂ :
    toute famille d'obligations admissible fournit la conclusion opaque. -/
def Det2TransportSignature : Prop :=
  ∀ o : Det2Obligations, Det2Admissible o → Det2TransportConclusion

/-- Sans admissibilité det₂, aucune conclusion ne peut être revendiquée
    conjointement avec les obligations. -/
theorem no_det2_claim_without_obligations
    (o : Det2Obligations) (h : ¬ Det2Admissible o) :
    ¬ (Det2Admissible o ∧ Det2TransportConclusion) := by
  intro ⟨ha, _⟩
  exact h ha

end CouretUnification.AnalyticHorizon
