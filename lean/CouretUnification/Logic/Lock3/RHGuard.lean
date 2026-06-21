/-
  CouretUnification.Logic.Lock3.RHGuard
  ════════════════════════════════════════════════════════════════════
  Garde-fou doctrinal : aucun objet local de la couche Lock 3 ne peut
  être promu vers une revendication de RH.

  Aligné avec `EpistemicDiscipline.DoctrinalInvariants.RHClaimed`
  (`Bool := false`), source canonique de la v38 unifiée.

  ────────────────────────────────────────────────────────────────────
  ADAPTATION v38 harmonisée
  ────────────────────────────────────────────────────────────────────

  Suite à la correction de `PhantomMass19` — paramétrage des trois
  propositions au niveau de la structure, plutôt que comme champs `Prop` —
  les variables implicites des théorèmes pare-feu sont étendues pour
  accepter les trois paramètres propositionnels.

  Doctrine : v38 harmonisée.
  Statut   : pare-feu, 0 sorry.
-/

import CouretUnification.Logic.Lock3.ProtectedTraceGate
import CouretUnification.EpistemicDiscipline.DoctrinalInvariants

open CouretUnification.EpistemicDiscipline

namespace CouretUnification.Logic.Lock3

/-! ## §1 — Ancrage du drapeau global de revendication RH -/

/--
Le drapeau de revendication RH, réexposé localement pour les théorèmes
pare-feu de Lock 3.

Cette réexportation ne redéfinit PAS `RHClaimed` — la source canonique est

  `EpistemicDiscipline.DoctrinalInvariants.RHClaimed : Bool`.

Elle rend seulement les théorèmes pare-feu lisibles dans ce namespace.
-/
theorem rh_not_claimed_lock3 : RHClaimed = false := rfl

/-! ## §2 — Théorèmes pare-feu -/

/--
Un verrou local Phantom 19 n'implique PAS RH.

Ce théorème est structurellement trivial — il ne fait que déplier
`RHClaimed = false` — mais son NOM et son EMPLACEMENT comptent
doctrinalement : tout chemin de code futur allant de `PhantomMass19`
vers RH devra d'abord franchir ce pare-feu.

Note : `PhantomMass19` est désormais paramétré par trois propositions
(`Defect19`, `ProtectedTrace`, `NoGlobalRHClaim`). Le pare-feu vaut pour
n'importe quel choix de ces trois propositions.
-/
theorem phantomMass19_does_not_claim_RH
    {R : LocalResidual}
    {C : AdmissibleCounterterm}
    {T : Lock3Thresholds}
    {Defect19 ProtectedTrace NoGlobalRHClaim : Prop}
    (_h : PhantomMass19 R C T Defect19 ProtectedTrace NoGlobalRHClaim) :
    RHClaimed = false := rfl

/--
Un certificat local Lock 3 n'implique PAS RH.

Même contenu logique que `phantomMass19_does_not_claim_RH`, mais nommé
séparément afin de tracer le point de pare-feu au niveau du certificat
plutôt qu'au niveau de la structure.
-/
theorem local_lock3_does_not_claim_RH
    {R : LocalResidual}
    {C : AdmissibleCounterterm}
    {T : Lock3Thresholds}
    (_h : Lock3Certified R C T) :
    RHClaimed = false := rfl

/--
Le témoin de vacuité issu de `LocalDebiasing` n'implique pas RH non plus.

C'est un pare-feu de paranoïa : même avec la reconnaissance EXPLICITE que
`Lock3Certified` est actuellement vacuous, il n'existe dans ce namespace
aucun chemin de « tout certifie trivialement » vers « RH ».
-/
theorem vacuous_certification_does_not_claim_RH
    (R : LocalResidual)
    (C : AdmissibleCounterterm)
    (T : Lock3Thresholds)
    (h_refinement : C.compatibleWithRefinement) :
    RHClaimed = false := by
  have _certified : Lock3Certified R C T :=
    Lock3Certified_is_currently_vacuous R C T h_refinement
  rfl

/-- Même la composition du témoin de vacuité avec le constructeur de
    `PhantomMass19` — en choisissant les trois propositions de garde comme
    `True` — n'implique pas RH. Cela ferme la dernière méta-brèche. -/
theorem vacuous_phantomMass19_does_not_claim_RH
    (R : LocalResidual)
    (C : AdmissibleCounterterm)
    (T : Lock3Thresholds)
    (h_refinement : C.compatibleWithRefinement) :
    RHClaimed = false := by
  have hCert : Lock3Certified R C T :=
    Lock3Certified_is_currently_vacuous R C T h_refinement
  have _hPM :
      PhantomMass19 R C T True True True :=
    protectedTraceStableAfterCounterterm
      R C T True True True hCert trivial trivial trivial
  rfl

end CouretUnification.Logic.Lock3
