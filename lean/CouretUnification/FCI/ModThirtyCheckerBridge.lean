/-
================================================================================
  FCI/ModThirtyCheckerBridge.lean
================================================================================
  Programme Couret-Unification · Couche FCI
  Cible effective : Lean 4.29.1 / Mathlib4

  RÔLE ──────────────────────────────────────────────────────────────────────────

  Bridge opérationnel entre le checker arithmétique mod 30 et une décision FCI
  minimale :

      ModThirtyChecker.toFCIOutput
          ↓
      FCIFact
          ↓
      fciDecide
          ↓
      FCIDecision

  Comme aucun `fciDecide` réel n'existait encore dans le dépôt au moment de
  cette remontée v38, ce fichier crée l'API canonique minimale :

    - `FCIFact`      : fait opérationnel transmis au Gate ;
    - `FCIDecision`  : décision abstraite du Gate ;
    - `fciDecide`    : règle refuse-by-default minimale ;
    - théorèmes de raccord avec `ModThirtyChecker`.

  CONTRAT DOCTRINAL ─────────────────────────────────────────────────────────────

  Le checker ne peut jamais forcer ALLOW.
  Il peut seulement :
    - ne rien ajouter au Gate (`allow` au sens "pas d'inhibition FCI locale") ;
    - demander une modulation (`modulate`) ;
    - forcer un rejet fail-close (`rejectFailClose`).

  RHClaimed = false.
-/

import CouretUnification.FCI.ModThirtyChecker
import Mathlib.Tactic

namespace FCI
namespace ModThirtyCheckerBridge

open ModThirtyChecker

/-! ## §1. Décision opérationnelle FCI minimale -/

/--
Décision abstraite du Gate FCI.

`allow` signifie ici : le checker mod 30 n'ajoute aucune inhibition locale.
Cela ne signifie pas autorisation globale du système complet.
-/
inductive FCIDecision where
  | allow
  | modulate
  | rejectFailClose
  deriving DecidableEq, Repr

/--
Fait opérationnel transmis au Gate FCI.

`mustViolations > 0` force le fail-close.
`inhibit = true` force au moins une modulation/inhibition locale.
-/
structure FCIFact where
  inhibit : Bool
  mustViolations : Nat
  evidence : Rat
  deriving Repr

/-! ## §2. Décideur FCI minimal -/

/--
Décision FCI minimale.

Priorité :
  1. toute violation MUST force `rejectFailClose` ;
  2. sinon, `inhibit = true` force `modulate` ;
  3. sinon, le checker ne force rien localement (`allow`).
-/
def fciDecide (f : FCIFact) : FCIDecision :=
  if f.mustViolations = 0 then
    if f.inhibit then .modulate else .allow
  else
    .rejectFailClose

theorem fciDecide_reject_of_mustViolations_nonzero
    (f : FCIFact)
    (h : f.mustViolations ≠ 0) :
    fciDecide f = .rejectFailClose := by
  simp [fciDecide, h]

theorem fciDecide_allow_of_clean
    (f : FCIFact)
    (hMust : f.mustViolations = 0)
    (hInhibit : f.inhibit = false) :
    fciDecide f = .allow := by
  simp [fciDecide, hMust, hInhibit]

theorem fciDecide_modulate_of_inhibit
    (f : FCIFact)
    (hMust : f.mustViolations = 0)
    (hInhibit : f.inhibit = true) :
    fciDecide f = .modulate := by
  simp [fciDecide, hMust, hInhibit]

theorem reject_implies_mustViolations_nonzero
    (f : FCIFact)
    (h : fciDecide f = .rejectFailClose) :
    f.mustViolations ≠ 0 := by
  intro hZero
  unfold fciDecide at h
  rw [hZero] at h
  by_cases hInh : f.inhibit = true <;> simp [hInh] at h

/-! ## §3. Raccord avec ModThirtyChecker -/

/--
Conversion du `CheckerOutput` concret vers un fait FCI opérationnel.
-/
def FCIFact.fromCheckerOutput (o : CheckerOutput) : FCIFact :=
  {
    inhibit := o.inhibit
    mustViolations := if o.mustFail then 1 else 0
    evidence := o.evidence
  }

/--
Fait FCI produit par le checker mod 30 sur un échantillon.
-/
def toFCIFact (s : Sample) : FCIFact :=
  FCIFact.fromCheckerOutput (toFCIOutput s)

/--
Décision FCI induite directement par le checker mod 30.
-/
def checkerFciDecide (s : Sample) : FCIDecision :=
  fciDecide (toFCIFact s)

/-! ## §4. Table de vérité du bridge -/

theorem nominal_to_allow
    (s : Sample)
    (h : checkSample s = .nominal) :
    checkerFciDecide s = .allow := by
  simp [checkerFciDecide, toFCIFact, FCIFact.fromCheckerOutput,
    toFCIOutput, fciDecide, h]

theorem suspect_to_allow
    (s : Sample)
    (h : checkSample s = .suspect) :
    checkerFciDecide s = .allow := by
  simp [checkerFciDecide, toFCIFact, FCIFact.fromCheckerOutput,
    toFCIOutput, fciDecide, h]

theorem anomaly_to_modulate
    (s : Sample)
    (h : checkSample s = .anomaly) :
    checkerFciDecide s = .modulate := by
  simp [checkerFciDecide, toFCIFact, FCIFact.fromCheckerOutput,
    toFCIOutput, fciDecide, h]

theorem critical_to_rejectFailClose
    (s : Sample)
    (h : checkSample s = .critical) :
    checkerFciDecide s = .rejectFailClose := by
  simp [checkerFciDecide, toFCIFact, FCIFact.fromCheckerOutput,
    toFCIOutput, fciDecide, h]

/-! ## §5. Théorèmes de sûreté opérationnelle -/

/--
Si κ² dépasse le seuil critique, le bridge opérationnel force le fail-close.
-/
theorem critical_kappa_forces_rejectFailClose
    (s : Sample)
    (h : kappaSquared s > kappaThresholdCritical) :
    checkerFciDecide s = .rejectFailClose := by
  have hMust : (toFCIOutput s).mustFail = true :=
    critical_forces_failclose s h
  simp [checkerFciDecide, toFCIFact, FCIFact.fromCheckerOutput,
    fciDecide, hMust]

/--
Le bridge ne peut pas produire un `mustViolation` sans inhibition.
-/
theorem checkerFact_mustViolation_implies_inhibit
    (s : Sample)
    (h : (toFCIFact s).mustViolations ≠ 0) :
    (toFCIFact s).inhibit = true := by
  cases hcs : checkSample s <;>
    simp [toFCIFact, FCIFact.fromCheckerOutput, toFCIOutput, hcs] at h ⊢

/--
Si le bridge aboutit à un rejet fail-close, alors le fait FCI correspondant
porte bien `inhibit = true`.
-/
theorem checkerReject_implies_inhibit
    (s : Sample)
    (h : checkerFciDecide s = .rejectFailClose) :
    (toFCIFact s).inhibit = true := by
  cases hcs : checkSample s <;>
    simp [checkerFciDecide, toFCIFact, FCIFact.fromCheckerOutput,
      toFCIOutput, fciDecide, hcs] at h ⊢

/--
Non-interférence opérationnelle :
le checker ne peut jamais transformer un état sans inhibition en rejet fort.
-/
theorem no_reject_without_inhibit
    (s : Sample)
    (hInhibit : (toFCIFact s).inhibit = false) :
    checkerFciDecide s ≠ .rejectFailClose := by
  intro hReject
  have hInhibitTrue : (toFCIFact s).inhibit = true :=
    checkerReject_implies_inhibit s hReject
  simp [hInhibit] at hInhibitTrue

/--
Préservation refuse-by-default au niveau du bridge :
toute violation MUST non nulle force le rejet.
-/
theorem fciFact_mustViolation_forces_reject
    (f : FCIFact)
    (h : f.mustViolations ≠ 0) :
    fciDecide f = .rejectFailClose :=
  fciDecide_reject_of_mustViolations_nonzero f h

/--
Le bridge est déterministe.
-/
theorem checkerFciDecide_deterministic
    (s : Sample) :
    checkerFciDecide s = checkerFciDecide s := rfl

/-! ## §6. Sanity checks -/

example (s : Sample) :
    checkerFciDecide s = fciDecide (toFCIFact s) := rfl

example (s : Sample)
    (h : checkSample s = .critical) :
    (toFCIFact s).mustViolations = 1 := by
  simp [toFCIFact, FCIFact.fromCheckerOutput, toFCIOutput, h]

example (s : Sample)
    (h : checkSample s = .anomaly) :
    (toFCIFact s).mustViolations = 0 ∧
    (toFCIFact s).inhibit = true := by
  simp [toFCIFact, FCIFact.fromCheckerOutput, toFCIOutput, h]

/-! ## §7. TODO / extensions

  [TODO-G1] Si une API FCI globale existe plus tard ailleurs dans le dépôt,
            remplacer ou raccorder `FCIFact`, `FCIDecision` et `fciDecide`
            à cette API.

  [TODO-G2] Ajouter un ledger typé des preuves/evidences si le pipeline EADX
            exige un journal certifié.

  [TODO-G3] Raffiner `.allow` en `.noLocalInhibition` si l'on veut éviter
            toute ambiguïté avec une autorisation globale du système complet.

-/

end ModThirtyCheckerBridge
end FCI