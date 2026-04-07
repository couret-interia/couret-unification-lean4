import CouretUnification.Core.TripletDocumentaryIntegralPowerPackage
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Objet compact canonique de référence du seul cas Couret :
on spécialise le paquet minimal arbitraire déjà construit
au triplet distingué, sans ouvrir de classification globale.
-/
structure CouretReferencePackage where
  package : TripletDocumentaryIntegralPowerPackage couretTriplet

/-- Paquet canonique de référence du cas Couret. -/
def couretReferencePackage : CouretReferencePackage where
  package := couretTripletDocumentaryIntegralPowerPackage

/-- Le candidat documentaire empaqueté est bien le `FiniteSpectrum` gelé de Couret. -/
theorem couretReferencePackage_candidate :
    couretReferencePackage.package.documentary.candidate = couretTripletSpectrum := by
  rfl

/-- Le certificat harmonique empaqueté est bien le certificat canonique du cas Couret. -/
theorem couretReferencePackage_harmonic :
    couretReferencePackage.package.documentary.harmonic =
      canonicalHarmonicCertificate couretTriplet := by
  rfl

/-- Le paquet de référence recolle bien avec l'historique documentaire. -/
theorem couretReferencePackage_matchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretReferencePackage.package.documentary.candidate := by
  exact couretReferencePackage.package.matchesHistorical

/-- Le paquet de référence porte bien l'intégralité harmonique minimale. -/
theorem couretReferencePackage_harmonicIntegral :
    certificateHasIntegralEntries
      couretReferencePackage.package.documentary.harmonic := by
  exact couretReferencePackage.package.harmonicIntegral

/-- Le paquet de référence porte bien l'intégralité finie documentaire. -/
theorem couretReferencePackage_documentaryIntegral :
    hasIntegralSpectrum
      couretReferencePackage.package.documentary.candidate := by
  exact couretReferencePackage.package.documentaryIntegral

/-- Le paquet de référence porte bien le recollement quadratique harmonique/documentaire. -/
theorem couretReferencePackage_powerMatchesHistorical :
    tripletPowerSpectrum couretTriplet =
      couretReferencePackage.package.documentary.candidate.powerHistorical.map
        (fun n => (n : ℝ)) := by
  exact couretReferencePackage.package.powerMatchesHistorical

/--
Validation groupée de l'objet compact canonique de référence du cas Couret :
- recollement harmonique/documentaire historique,
- intégralité harmonique minimale,
- intégralité finie documentaire,
- recollement quadratique harmonique/documentaire.
-/
theorem couretReferencePackage_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretReferencePackage.package.documentary.candidate
      ∧ certificateHasIntegralEntries
          couretReferencePackage.package.documentary.harmonic
      ∧ hasIntegralSpectrum
          couretReferencePackage.package.documentary.candidate
      ∧ tripletPowerSpectrum couretTriplet =
          couretReferencePackage.package.documentary.candidate.powerHistorical.map
            (fun n => (n : ℝ)) := by
  exact ⟨ couretReferencePackage_matchesHistorical
        , couretReferencePackage_harmonicIntegral
        , couretReferencePackage_documentaryIntegral
        , couretReferencePackage_powerMatchesHistorical ⟩

end

end CouretUnification.Core