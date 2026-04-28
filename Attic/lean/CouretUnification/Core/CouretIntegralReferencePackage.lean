import CouretUnification.Core.TripletIntegralCandidateInterface
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Objet compact canonique de référence du seul cas Couret :
on spécialise l’interface intégrale candidate déjà construite
au triplet distingué, sans ouvrir de classification globale.
-/
structure CouretIntegralReferencePackage where
  interface : TripletIntegralCandidateInterface couretTriplet

/-- Paquet canonique intégral de référence du cas Couret. -/
def couretIntegralReferencePackage : CouretIntegralReferencePackage where
  interface := couretTripletIntegralCandidateInterface

/-- Le candidat documentaire empaqueté est bien le `FiniteSpectrum` gelé de Couret. -/
theorem couretIntegralReferencePackage_candidate :
    couretIntegralReferencePackage.interface.candidate.documentary.candidate =
      couretTripletSpectrum := by
  rfl

/-- Le certificat harmonique empaqueté est bien le certificat canonique du cas Couret. -/
theorem couretIntegralReferencePackage_harmonic :
    couretIntegralReferencePackage.interface.candidate.documentary.harmonic =
      canonicalHarmonicCertificate couretTriplet := by
  rfl

/-- Le paquet de référence recolle bien avec l’historique documentaire. -/
theorem couretIntegralReferencePackage_matchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretIntegralReferencePackage.interface.candidate.documentary.candidate := by
  exact couretIntegralReferencePackage.interface.matchesHistorical

/-- Le paquet de référence recolle bien quadratiquement avec l’historique documentaire. -/
theorem couretIntegralReferencePackage_matchesHistoricalPower :
    tripletPowerSpectrum couretTriplet =
      couretIntegralReferencePackage.interface.candidate.documentary.candidate.powerHistorical.map
        (fun n => (n : ℝ)) := by
  exact couretIntegralReferencePackage.interface.matchesHistoricalPower

/-- Le paquet de référence porte bien l’intégralité harmonique minimale. -/
theorem couretIntegralReferencePackage_harmonicIntegral :
    certificateHasIntegralEntries
      couretIntegralReferencePackage.interface.candidate.documentary.harmonic := by
  exact couretIntegralReferencePackage.interface.harmonicIntegral

/-- Le paquet de référence porte bien l’intégralité finie documentaire. -/
theorem couretIntegralReferencePackage_documentaryIntegral :
    hasIntegralSpectrum
      couretIntegralReferencePackage.interface.candidate.documentary.candidate := by
  exact couretIntegralReferencePackage.interface.documentaryIntegral

/--
Validation groupée de l’objet compact canonique intégral de référence du cas Couret :
- recollement harmonique/documentaire historique,
- recollement quadratique harmonique/documentaire,
- intégralité harmonique minimale,
- intégralité finie documentaire.
-/
theorem couretIntegralReferencePackage_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretIntegralReferencePackage.interface.candidate.documentary.candidate
      ∧ tripletPowerSpectrum couretTriplet =
          couretIntegralReferencePackage.interface.candidate.documentary.candidate.powerHistorical.map
            (fun n => (n : ℝ))
      ∧ certificateHasIntegralEntries
          couretIntegralReferencePackage.interface.candidate.documentary.harmonic
      ∧ hasIntegralSpectrum
          couretIntegralReferencePackage.interface.candidate.documentary.candidate := by
  exact ⟨ couretIntegralReferencePackage_matchesHistorical
        , couretIntegralReferencePackage_matchesHistoricalPower
        , couretIntegralReferencePackage_harmonicIntegral
        , couretIntegralReferencePackage_documentaryIntegral ⟩

end

end CouretUnification.Core