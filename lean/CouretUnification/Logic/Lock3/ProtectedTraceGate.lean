/-
  CouretUnification.Logic.Lock3.ProtectedTraceGate
  ════════════════════════════════════════════════════════════════════
  Promotion logique d'un candidat Lock 2 à un objet Lock 3 localement
  verrouillé. Cette promotion N'EST PAS une preuve analytique de RH.

  Architecture :
    candidate (Lock 2) → biasedPlateau → locallyLocked (Lock 3) → rejected

  ────────────────────────────────────────────────────────────────────
  CORRECTION v38 harmonisée
  ────────────────────────────────────────────────────────────────────

  Dans la v38.1 enrichi, la structure `PhantomMass19` portait trois
  champs de type `Prop` :
      defect_is_19           : Prop
      protected_trace_target : Prop
      no_global_RH_claim     : Prop
  C'est universellement incorrect : un champ de type `Prop` (où le
  type EST `Prop`, qui vit dans `Type 0`) interdit à la structure
  d'habiter `Prop` elle-même. Lean 4 promeut alors PhantomMass19 à
  `Type`, ce qui n'est pas l'intention doctrinale (PhantomMass19
  doit être un *énoncé*, pas une donnée).

  La forme correcte, conservée ici, paramètre la structure par les
  trois propositions et exige des PREUVES de ces propositions :
      structure PhantomMass19 (... ) (D PT NR : Prop) : Prop where
        defect_is_19_proof          : D
        protected_trace_target_proof : PT
        no_global_RH_claim_proof    : NR

  Ainsi PhantomMass19 reste honnêtement dans `Prop`, et chaque champ
  est une obligation de preuve fournie par l'utilisateur de la
  promotion.

  Doctrine : v38 harmonisée
  Status   : interface logique, 0 sorry.
-/

import CouretUnification.Logic.Lock3.LocalDebiasing

namespace CouretUnification.Logic.Lock3

/-! ## §1 — Local lock status -/

/--
Local status of the Lock 3 gate.

  candidate     — Lock 2 reached, residual identified
  biasedPlateau — counterterm hypothesised but not yet certified
  locallyLocked — Lock 3 certified locally (under current thresholds)
  rejected      — certification failed
-/
inductive LocalLockStatus where
  | candidate
  | biasedPlateau
  | locallyLocked
  | rejected
deriving DecidableEq, Repr

/-! ## §2 — Locally locked Phantom 19 object -/

/--
A locally locked Phantom 19 object.

This does NOT claim RH. It only says that the local Lock 3 gate has
been crossed under the declared thresholds and admissible counterterm,
modulo the four interface predicates of `LocalDebiasing` (currently
vacuous — see `Lock3Certified_is_currently_vacuous`).

The structure is parametrised by three propositions, each of which
must be proved by the user of the promotion :
  - `Defect19`           : the residual is attributed to phantom 19
  - `ProtectedTrace`     : the protected trace candidate -12 is in scope
  - `NoGlobalRHClaim`    : the local lock does NOT promote to RH

Field naming : `*_proof` to make the obligation explicit.
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
Promotion from Lock 2 candidate to Lock 3 locally locked.

This is a logical promotion (a function from a certificate to a
status enum), not an analytic proof of RH. The certificate itself
remains conditional on the refinement of the four interface predicates.
-/
def promoteToLock3
    (R : LocalResidual)
    (C : AdmissibleCounterterm)
    (T : Lock3Thresholds)
    (_h : Lock3Certified R C T) :
    LocalLockStatus :=
  LocalLockStatus.locallyLocked

/--
If the Lock 3 certificate is available, one may build a local
`PhantomMass19` object, provided proofs of the three guard
propositions are supplied.

This is a constructive packaging, not a proof of any analytic content.
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
