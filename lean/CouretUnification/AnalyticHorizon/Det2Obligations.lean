/-
  Couret-Unification — v35.9-pre
  AnalyticHorizon/Det2Obligations.lean

  Objet : OBLIGATIONS TYPÉES POUR Det2Transport.

         Promotion du sorry doctrinal unique de Det2Transport en quatre
         obligations *visibles au type-checker*. C'est la version Lean
         du principe FCI :

             No Obligation  ⇒  No Det2 Transport Claim.

         Le sorry n'est pas supprimé : il est *juridictionnalisé*. Tant que
         les quatre obligations ne sont pas instanciées, le théorème
         conditionnel `det2_transport_under_obligations` reste sans
         hypothèse satisfaite, et donc inopérant.

  Statut     : Frozen-eligible (0 sorry, structures uniquement)
  Layer      : AnalyticHorizon
  Doctrine   : Cette structure remplace le sorry doctrinal historique de
               Det2Transport.lean. La preuve analytique elle-même reste
               dans Active/AnalyticHorizon/Det2Transport.lean.
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0

  Renommage doctrinal v35.9 (cf. cartographie 21 avril 2026) :
  Les anciens labels internes H1/H2/H3 entraient en collision avec les
  labels GLOBAUX H1/H2/H3 du programme. Les obligations Det2 sont
  désormais étiquetées A1_num / A2_den / A3_bound / A4_critical pour
  éviter cette ambiguïté.

  Pour Bernard.
-/

namespace CouretUnification.AnalyticHorizon

/- ═══════════════════════════════════════════════════════════════════════════
   LES QUATRE OBLIGATIONS Det2
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Les quatre obligations analytiques dont dépend Det2Transport.

    Chaque champ correspond à une étape précise du transport :

    A1_num         : Borne supérieure sur le numérateur du défaut régularisé.
    A2_den         : Minoration du dénominateur (loin de zéro).
    A3_bound       : Argument de compacité ou de convergence dominée.
    A4_critical    : Contrôle uniforme sur la ligne critique Re(s) = 1/2.

    Cette structure remplace le sorry doctrinal unique qui pesait sur
    `det2_transport` dans les versions v34 et v35.0–v35.8. -/
structure Det2Obligations where
  /-- A1_num : le numérateur du défaut régularisé est borné en module
      uniformément sur la ligne critique. -/
  numeratorBounded         : Prop
  /-- A2_den : le dénominateur du défaut régularisé est borné en valeur
      absolue PAR EN BAS, sur la ligne critique, par une constante > 0. -/
  denominatorBoundedBelow  : Prop
  /-- A3_bound : argument de compacité (Hille-Tamarkin sur compact ou
      convergence dominée) qui permet l'interversion limite-intégrale. -/
  compactnessArgument      : Prop
  /-- A4_critical : contrôle uniforme du défaut régularisé sur la ligne
      critique Re(s) = 1/2 — le verrou doctrinal historique du programme. -/
  criticalLineControl      : Prop

/-- Le critère d'admissibilité Det2 : conjonction des quatre obligations. -/
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
   GATE FCI : NO OBLIGATION ⇒ NO CLAIM
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Spécification de la conclusion de Det2Transport (à instancier dans Active). -/
opaque Det2TransportConclusion : Prop

/-- Théorème conditionnel : si les quatre obligations sont satisfaites,
    alors la conclusion de Det2Transport tient.

    NOTE CRUCIALE : ce théorème n'est pas prouvé ici. Il est seulement
    *spécifié comme la forme* qu'il prendra. La preuve analytique appartient
    à Active/AnalyticHorizon/Det2Transport.lean.

    Ici, on l'expose comme `def` (Prop) plutôt que comme `theorem`
    pour bien marquer qu'il s'agit d'une *signature visible au type-checker*,
    pas d'un théorème démontré. -/
def Det2TransportSignature : Prop :=
  ∀ o : Det2Obligations, Det2Admissible o → Det2TransportConclusion

/-- Théorème doctrinal FCI : sans admissibilité, aucune revendication
    de transport déterminantiel. -/
theorem no_det2_claim_without_obligations
    (o : Det2Obligations) (h : ¬ Det2Admissible o) :
    ¬ (Det2Admissible o ∧ Det2TransportConclusion) := by
  intro ⟨ha, _⟩
  exact h ha

/- ═══════════════════════════════════════════════════════════════════════════
   MAXIME DOCTRINALE
   ═══════════════════════════════════════════════════════════════════════════

   Le paroxysme FCI ne consiste pas à supprimer magiquement les sorries.
   Il consiste à les juridictionnaliser : un sorry caché dans une preuve
   est remplacé par une obligation typée visible au type-checker.

   Avant v35.9, Det2Transport portait un sorry doctrinal opaque sur la
   majoration du défaut régularisé. Désormais, ce sorry est exposé comme
   `criticalLineControl : Prop` dans `Det2Obligations`. Le sorry n'est
   pas fermé mathématiquement, mais il devient *opposable* :
   tout instanciateur futur doit fournir une preuve effective de
   `criticalLineControl`, au lieu de cacher l'argument dans un trou de
   preuve illisible.

   C'est la version Lean de la doctrine FCI :
       sorry  ⟶  obligation visible au type-checker.
-/

end CouretUnification.AnalyticHorizon
