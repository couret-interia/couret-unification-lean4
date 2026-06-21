/-
  CouretUnification.Logic.Lock3.ProtectedTraceGate
  ════════════════════════════════════════════════════════════════════
  Promotion logique d'un candidat Lock 2 vers un objet Lock 3 localement
  verrouillé. Cette promotion N'EST PAS une preuve analytique de RH.

  Architecture :
    candidate (Lock 2) → biasedPlateau → locallyLocked (Lock 3) → rejected

  ────────────────────────────────────────────────────────────────────
  CORRECTION v38 harmonisée
  ────────────────────────────────────────────────────────────────────

  Dans la v38.1 enrichie, la structure `PhantomMass19` portait trois
  champs de type `Prop` :
      defect_is_19           : Prop
      protected_trace_target : Prop
      no_global_RH_claim     : Prop

  C'est universellement incorrect : un champ de type `Prop` — où le
  type EST `Prop`, qui vit dans `Type 0` — interdit à la structure
  d'habiter `Prop` elle-même. Lean 4 promeut alors `PhantomMass19` à
  `Type`, ce qui n'est pas l'intention doctrinale : `PhantomMass19`
  doit être un *énoncé*, non une donnée.

  La forme correcte, conservée ici, paramètre la structure par les
  trois propositions et exige des PREUVES de ces propositions :
      structure PhantomMass19 (... ) (D PT NR : Prop) : Prop where
        defect_is_19_proof           : D
        protected_trace_target_proof : PT
        no_global_RH_claim_proof     : NR

  Ainsi `PhantomMass19` reste honnêtement dans `Prop`, et chaque champ
  devient une obligation de preuve fournie par l'utilisateur de la
  promotion.

  Doctrine : v38 harmonisée.
  Statut   : interface logique, 0 sorry.
-/

import CouretUnification.Logic.Lock3.LocalDebiasing

namespace CouretUnification.Logic.Lock3

/-! ## §1 — Statut local du verrou -/

/--
Statut local de la porte Lock 3.

  candidate     — Lock 2 atteint, résidu identifié.
  biasedPlateau — contreterme hypothétisé mais pas encore certifié.
  locallyLocked — Lock 3 certifié localement, sous les seuils courants.
  rejected      — certification échouée.
-/
inductive LocalLockStatus where
  | candidate
  | biasedPlateau
  | locallyLocked
  | rejected
deriving DecidableEq, Repr

/-! ## §2 — Objet Phantom 19 localement verrouillé -/

/--
Un objet Phantom 19 localement verrouillé.

Cela ne revendique PAS RH. Cela affirme seulement que la porte locale
Lock 3 a été franchie sous les seuils déclarés et avec un contreterme
admissible, modulo les quatre prédicats d'interface de `LocalDebiasing`
— actuellement vacuous ; voir `Lock3Certified_is_currently_vacuous`.

La structure est paramétrée par trois propositions, chacune devant être
prouvée par l'utilisateur de la promotion :

  - `Defect19`        : le résidu est attribué au fantôme 19 ;
  - `ProtectedTrace`  : la cible de trace protégée `-12` est dans le cadre ;
  - `NoGlobalRHClaim` : le verrou local ne promeut PAS vers RH.

Nommage des champs : `*_proof`, afin de rendre l'obligation explicite.
-/
structure PhantomMass19
    (R : LocalResidual)
    (C : AdmissibleCounterterm)
    (T : Lock3Thresholds)
    (Defect19 ProtectedTrace NoGlobalRHClaim : Prop) : Prop where
  lock3 :
    Lock3Certified R C T
  defect_is_19_proof :
    Defect19
  protected_trace_target_proof :
    ProtectedTrace
  no_global_RH_claim_proof :
    NoGlobalRHClaim

/-! ## §3 — Promotion -/

/--
Promotion d'un candidat Lock 2 vers un objet Lock 3 localement verrouillé.

Il s'agit d'une promotion logique — une fonction d'un certificat vers une
énumération de statut — et non d'une preuve analytique de RH.

Le certificat lui-même reste conditionnel au raffinement des quatre
prédicats d'interface.
-/
def promoteToLock3
    (R : LocalResidual)
    (C : AdmissibleCounterterm)
    (T : Lock3Thresholds)
    (_h : Lock3Certified R C T) :
    LocalLockStatus :=
  LocalLockStatus.locallyLocked

/--
Si le certificat Lock 3 est disponible, on peut construire un objet local
`PhantomMass19`, à condition de fournir les preuves des trois propositions
de garde.

C'est un emballage constructif, non une preuve de contenu analytique.
-/
theorem protectedTraceStableAfterCounterterm
    (R : LocalResidual)
    (C : AdmissibleCounterterm)
    (T : Lock3Thresholds)
    (Defect19 ProtectedTrace NoGlobalRHClaim : Prop)
    (hLock : Lock3Certified R C T)
    (hDefect : Defect19)
    (hTrace : ProtectedTrace)
    (hNoRH : NoGlobalRHClaim) :
    PhantomMass19 R C T Defect19 ProtectedTrace NoGlobalRHClaim :=
  { lock3 := hLock
    defect_is_19_proof := hDefect
    protected_trace_target_proof := hTrace
    no_global_RH_claim_proof := hNoRH }

end CouretUnification.Logic.Lock3
