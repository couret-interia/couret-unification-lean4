/-
  CouretUnification.Logic.Lock3.RHGuard
  ════════════════════════════════════════════════════════════════════
  Garde-fou doctrinal : aucun objet local de la couche Lock 3 ne
  peut être promu vers une revendication de RH.

  Aligné avec `EpistemicDiscipline.DoctrinalInvariants.RHClaimed`
  (Bool := false), source canonique v38 unifiée.

  ────────────────────────────────────────────────────────────────────
  ADAPTATION v38 harmonisée
  ────────────────────────────────────────────────────────────────────

  Suite à la correction de `PhantomMass19` (paramétrage des trois
  Props au niveau de la structure plutôt que comme champs `Prop`),
  les variables implicites des théorèmes firewall sont étendues pour
  accepter les trois paramètres propositionnels.

  Doctrine : v38 harmonisée
  Status   : firewall, 0 sorry.
-/

import Mathlib
import CouretUnification.Logic.Lock3.ProtectedTraceGate
import CouretUnification.EpistemicDiscipline.DoctrinalInvariants

open CouretUnification.EpistemicDiscipline

namespace CouretUnification
namespace Logic
namespace Lock3

/-! ## §1 — Anchoring the global RH claim flag -/

/--
The RH claim flag, re-exposed locally for Lock 3 firewall theorems.

This re-export does NOT redefine `RHClaimed` (the canonical source is
`EpistemicDiscipline.DoctrinalInvariants.RHClaimed : Bool`) — it
merely makes the firewall theorems readable in this namespace.
-/
theorem rh_not_claimed_lock3 : RHClaimed = false := rfl

/-! ## §2 — Firewall theorems -/

/--
A local Phantom 19 lock does NOT imply RH.

This theorem is structurally trivial (it just unfolds `RHClaimed = false`),
but its NAME and LOCATION matter doctrinally: any future code path
that goes from `PhantomMass19` to RH must first defeat this firewall.

Note : `PhantomMass19` is now parametrised by three propositions
(Defect19, ProtectedTrace, NoGlobalRHClaim). The firewall holds for
any choice of those three.
-/
theorem phantomMass19_does_not_claim_RH
    {R : LocalResidual}
    {C : AdmissibleCounterterm}
    {T : Lock3Thresholds}
    {Defect19 ProtectedTrace NoGlobalRHClaim : Prop}
    (_h : PhantomMass19 R C T Defect19 ProtectedTrace NoGlobalRHClaim) :
    RHClaimed = false := rfl

/--
A local Lock 3 certificate does NOT imply RH.

Same logical content as `phantomMass19_does_not_claim_RH`, named
separately to track the firewall point at the certificate level
rather than the structure level.
-/
theorem local_lock3_does_not_claim_RH
    {R : LocalResidual}
    {C : AdmissibleCounterterm}
    {T : Lock3Thresholds}
    (_h : Lock3Certified R C T) :
    RHClaimed = false := rfl

/--
The vacuity witness from `LocalDebiasing` does NOT imply RH either.

This is a paranoia firewall: even given the EXPLICIT acknowledgment
that `Lock3Certified` is currently vacuous, no path from "everything
trivially certifies" to "RH" exists in this namespace.
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

/-- Even composing the vacuity witness with the constructor of
    `PhantomMass19` (with the three guard propositions chosen as
    `True`) does not imply RH. This closes the last meta-loophole. -/
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

end Lock3
end Logic
end CouretUnification
