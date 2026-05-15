/-
  CouretUnification.AnalyticHorizon.ProtectedMinusTraceTargets
  ════════════════════════════════════════════════════════════════════
  Trace compressée sur le secteur de défaut E(-1) — le candidat
  d'invariant qui SURVIT à la perturbation Legendre.

  Au niveau q=30 :         Tr(P_- A^{nt} P_-) = -12
  Au niveau q générique :  trace brute dilate (-12 · N_q)
                          mais densité normalisée stable à -4

  Distinction doctrinale critique :
    P_- est un projecteur SPECTRAL (sur E_{-1}, sous-espace de v.p. -1)
    P_19 serait un projecteur GÉOMÉTRIQUE (sur le résidu 19 dans G_30)
  Les deux ne sont PAS identifiés en Lean sans preuve.

  Doctrine : v38 unifiée, commit 4
-/

import Mathlib.Tactic.ComputeAsymptotics.Lemmas
import CouretUnification.AnalyticHorizon.TraceFormulaTargets

open CouretUnification.EpistemicDiscipline

namespace CouretUnification.AnalyticHorizon

/--
Protected compressed trace on the defect sector E(-1).

Doctrine:
This is not a global moment invariant.
It is a local invariant candidate on the punctured-Klein defect sector.
-/
def ProtectedMinusTrace30 : ℚ := -12

/--
Raw lifted protected trace.

At CRT scale Nq, the raw trace dilates as -12 * Nq.
The normalized density is expected to remain stable.
-/
def ProtectedMinusTraceLift (Nq : ℚ) : ℚ := -12 * Nq

/-- Trivial-sector trace scale: 3 * Nq. -/
def TrivialSectorTraceLift (Nq : ℚ) : ℚ := 3 * Nq

/-- Stable normalized defect ratio. -/
theorem protected_trace_normalized_ratio (Nq : ℚ) (hN : Nq ≠ 0) :
    ProtectedMinusTraceLift Nq / TrivialSectorTraceLift Nq = -4 := by
  unfold ProtectedMinusTraceLift TrivialSectorTraceLift
  field_simp
  ring

/-- The protected trace is the preferred scalar invariant after Legendre perturbation. -/
def ProtectedMinusTraceOK : BridgeStatus := BridgeStatus.theoremTarget

/-- Global moment rigidity is demoted after Legendre perturbation. -/
def TensorialMomentRigidityOnly : Bool := true

/-- The protected trace is preferred over global scalar moments. -/
def ProtectedTracePreferredOverGlobalMoments : Bool := true

theorem protected_minus_trace_30_value :
    ProtectedMinusTrace30 = -12 := rfl

theorem protected_minus_trace_status :
    ProtectedMinusTraceOK = BridgeStatus.theoremTarget := rfl

theorem tensorial_moments_demoted :
    TensorialMomentRigidityOnly = true := rfl

theorem protected_trace_preferred :
    ProtectedTracePreferredOverGlobalMoments = true := rfl

/-- Concrete lift values at the primorial tower. -/
theorem protected_lift_at_210 :
    ProtectedMinusTraceLift 6 = -72 := by
  norm_num [ProtectedMinusTraceLift]

theorem protected_lift_at_2310 :
    ProtectedMinusTraceLift 60 = -720 := by
  norm_num [ProtectedMinusTraceLift]

theorem no_rh_from_protected_minus_trace :
    RHClaimed = false := rfl

end CouretUnification.AnalyticHorizon
