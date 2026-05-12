-- =========================================================================
-- Couret-Unification / TowerLift v18
-- Module : Numerics/UseScanSummary.lean
--
-- Façade d'utilisation du résumé numérique TowerLift.
--
-- Version v38x corrigée :
--   - la proximité spectrale forte est disponible ;
--   - la stabilité numérique faible n'est PAS disponible ;
--   - le verdict global est donc : spectralement proche, mais couplage
--     faible non stable au seuil choisi.
-- =========================================================================

import CouretUnification.Numerics.ScanSummary

namespace CouretUnification

open CouretUnification.Numerics

def SGNumericallyStable : Prop :=
  NumericalWeakCouplingStable

def SGVeryNumericallyStable : Prop :=
  NumericalWeakCouplingVeryStable

def SGSpectrallyCloseToLambda : Prop :=
  StrongSpectralProximity

def SGVerySpectrallyCloseToLambda : Prop :=
  VeryStrongSpectralProximity

/-- Ancien verdict positif, conservé comme proposition mais non prouvé :
    il est faux avec les constantes actuelles, car `toyMuPosCV = 1.2715...`. -/
def SGScanSummaryOK : Prop :=
  SGNumericallyStable ∧ SGSpectrallyCloseToLambda

/-- Verdict corrigé : proximité spectrale forte, mais absence de stabilité
    numérique faible au seuil 0.10. -/
def SGScanSummaryVerdict : Prop :=
  SGSpectrallyCloseToLambda ∧ ¬ SGNumericallyStable

theorem SG_scan_verdict : SGScanSummaryVerdict := by
  exact scanSummary_verdict

theorem sg_numerical_stability_not_available : ¬ SGNumericallyStable := by
  exact not_NumericalWeakCouplingStable

theorem sg_very_numerical_stability_not_available : ¬ SGVeryNumericallyStable := by
  exact not_NumericalWeakCouplingVeryStable

theorem sg_spectral_proximity_available : SGSpectrallyCloseToLambda := by
  exact sgSpectralProximity

theorem sg_very_spectral_proximity_not_available : ¬ SGVerySpectrallyCloseToLambda := by
  exact not_veryStrongSpectralProximity

/-- L'ancien verdict `SGScanSummaryOK` est réfuté par l'échec de la stabilité
    numérique faible. -/
theorem SG_scan_summary_ok_refuted : ¬ SGScanSummaryOK := by
  intro h
  exact sg_numerical_stability_not_available h.1

end CouretUnification