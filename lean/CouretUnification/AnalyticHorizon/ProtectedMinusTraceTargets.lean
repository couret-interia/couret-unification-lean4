/-
  CouretUnification.AnalyticHorizon.ProtectedMinusTraceTargets
  ════════════════════════════════════════════════════════════════════
  Cibles de trace protégée sur le secteur de défaut E(-1).

  Ce fichier encode le candidat d'invariant scalaire qui SURVIT à la
  perturbation de Legendre : la trace compressée sur le secteur spectral
  de défaut.

  Valeur de base
  --------------
  Au niveau q = 30 :

      Tr(P_- · A^{nt} · P_-) = -12.

  Relèvement CRT
  --------------
  Au niveau q générique, la trace brute se dilate comme

      -12 · N_q,

  tandis que la densité normalisée par rapport au secteur trivial reste
  stable à

      -4.

  Distinction doctrinale critique
  -------------------------------
    • P_- :
        projecteur SPECTRAL sur E_{-1}, le sous-espace de valeur propre -1.

    • P_19 :
        projecteur GÉOMÉTRIQUE sur le résidu 19 dans G_30.

  Ces deux projecteurs ne sont PAS identifiés en Lean sans preuve.

  Rôle
  ----
  Ce fichier :
    • pose la cible scalaire protégée `ProtectedMinusTrace30 = -12` ;
    • encode son relèvement brut `ProtectedMinusTraceLift` ;
    • prouve le rapport normalisé stable `-4` ;
    • documente la rétrogradation des moments tensoriels globaux ;
    • affirme la préférence doctrinale pour la trace protégée.

  Garde-fous
  ----------
    • aucune représentation concrète P_- / A^{nt} n'est construite ici ;
    • aucune trace matricielle concrète n'est calculée ici ;
    • aucune identification P_- = P_19 n'est affirmée ;
    • aucune rigidité globale des moments n'est revendiquée ;
    • aucune conséquence RH n'est exportée.

  Doctrine : v38 unifiée, commit 4.
-/

import Mathlib.Tactic.ComputeAsymptotics.Lemmas
import CouretUnification.AnalyticHorizon.TraceFormulaTargets

open CouretUnification.EpistemicDiscipline

namespace CouretUnification.AnalyticHorizon

/--
Trace compressée protégée sur le secteur de défaut E(-1).

Doctrine :
ce n'est pas un invariant global de moment. C'est un candidat d'invariant
local sur le secteur de défaut du Klein ponctué.
-/
def ProtectedMinusTrace30 : ℚ := -12

/--
Trace protégée brute relevée.

À l'échelle CRT `Nq`, la trace brute se dilate comme `-12 * Nq`.
La densité normalisée est attendue comme stable.
-/
def ProtectedMinusTraceLift (Nq : ℚ) : ℚ := -12 * Nq

/-- Échelle de trace du secteur trivial : `3 * Nq`.

    Ce facteur sert de normalisation pour comparer la trace protégée
    relevée au secteur trivial. -/
def TrivialSectorTraceLift (Nq : ℚ) : ℚ := 3 * Nq

/-- Rapport de défaut normalisé stable.

    Pour `Nq ≠ 0`, le quotient de la trace protégée relevée par l'échelle
    du secteur trivial vaut exactement `-4`. -/
theorem protected_trace_normalized_ratio (Nq : ℚ) (hN : Nq ≠ 0) :
    ProtectedMinusTraceLift Nq / TrivialSectorTraceLift Nq = -4 := by
  unfold ProtectedMinusTraceLift TrivialSectorTraceLift
  field_simp
  ring

/-- La trace protégée est l'invariant scalaire préféré après perturbation
    de Legendre.

    Statut actuel : `theoremTarget`, car la représentation matricielle
    concrète n'est pas encore raccordée. -/
def ProtectedMinusTraceOK : BridgeStatus := BridgeStatus.theoremTarget

/-- La rigidité globale des moments est rétrogradée après perturbation
    de Legendre.

    Les moments tensoriels globaux ne sont conservés que comme régime
    tensorial-only, non comme pont global. -/
def TensorialMomentRigidityOnly : Bool := true

/-- La trace protégée est préférée aux moments scalaires globaux. -/
def ProtectedTracePreferredOverGlobalMoments : Bool := true

/-- Vérification statique de la valeur de base au niveau q = 30. -/
theorem protected_minus_trace_30_value :
    ProtectedMinusTrace30 = -12 := rfl

/-- Vérification statique du statut de la cible de trace protégée. -/
theorem protected_minus_trace_status :
    ProtectedMinusTraceOK = BridgeStatus.theoremTarget := rfl

/-- Vérification statique : les moments tensoriels globaux sont rétrogradés. -/
theorem tensorial_moments_demoted :
    TensorialMomentRigidityOnly = true := rfl

/-- Vérification statique : la trace protégée est l'invariant préféré. -/
theorem protected_trace_preferred :
    ProtectedTracePreferredOverGlobalMoments = true := rfl

/-- Valeur concrète du relèvement au niveau q = 210, avec `Nq = 6`. -/
theorem protected_lift_at_210 :
    ProtectedMinusTraceLift 6 = -72 := by
  norm_num [ProtectedMinusTraceLift]

/-- Valeur concrète du relèvement au niveau q = 2310, avec `Nq = 60`. -/
theorem protected_lift_at_2310 :
    ProtectedMinusTraceLift 60 = -720 := by
  norm_num [ProtectedMinusTraceLift]

/-- Pare-feu doctrinal : la cible de trace protégée ne revendique pas RH. -/
theorem no_rh_from_protected_minus_trace :
    RHClaimed = false := rfl

end CouretUnification.AnalyticHorizon
