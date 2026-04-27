import CouretUnification.Core.TripletQuadraticIntegralCandidateInterface
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Objet compact canonique de référence du seul cas Couret :
on spécialise l’interface quadratique intégrale candidate déjà construite
au triplet distingué, sans ouvrir de classification globale.
-/
structure CouretQuadraticIntegralReferencePackage where
  interface : TripletQuadraticIntegralCandidateInterface couretTriplet

/-- Paquet canonique quadratique intégral de référence du cas Couret. -/
def couretQuadraticIntegralReferencePackage :
    CouretQuadraticIntegralReferencePackage where
  interface := couretTripletQuadraticIntegralCandidateInterface

/-- Le candidat documentaire empaqueté est bien le `FiniteSpectrum` gelé de Couret. -/
theorem couretQuadraticIntegralReferencePackage_candidate :
    couretQuadraticIntegralReferencePackage.interface.quadratic.candidate.documentary.candidate =
      couretTripletSpectrum := by
  rfl

/-- Le certificat harmonique empaqueté est bien le certificat canonique du cas Couret. -/
theorem couretQuadraticIntegralReferencePackage_harmonic :
    couretQuadraticIntegralReferencePackage.interface.quadratic.candidate.documentary.harmonic =
      canonicalHarmonicCertificate couretTriplet := by
  rfl

/-- Le paquet de référence recolle bien avec l’historique documentaire. -/
theorem couretQuadraticIntegralReferencePackage_matchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretQuadraticIntegralReferencePackage.interface.quadratic.candidate.documentary.candidate := by
  exact couretQuadraticIntegralReferencePackage.interface.matchesHistorical

/-- Le paquet de référence réalise bien le calcul quadratique harmonique. -/
theorem couretQuadraticIntegralReferencePackage_realizesPower :
    couretQuadraticIntegralReferencePackage.interface.quadratic.powerCoeffs =
      tripletPowerSpectrum couretTriplet := by
  exact couretQuadraticIntegralReferencePackage.interface.realizesPower

/-- Le paquet de référence recolle bien quadratiquement avec l’historique documentaire. -/
theorem couretQuadraticIntegralReferencePackage_matchesHistoricalPower :
    couretQuadraticIntegralReferencePackage.interface.quadratic.powerCoeffs =
      couretQuadraticIntegralReferencePackage.interface.quadratic.candidate.documentary.candidate.powerHistorical.map
        (fun n => (n : ℝ)) := by
  exact couretQuadraticIntegralReferencePackage.interface.matchesHistoricalPower

/-- Le paquet de référence porte bien l’intégralité harmonique minimale. -/
theorem couretQuadraticIntegralReferencePackage_harmonicIntegral :
    certificateHasIntegralEntries
      couretQuadraticIntegralReferencePackage.interface.quadratic.candidate.documentary.harmonic := by
  exact couretQuadraticIntegralReferencePackage.interface.harmonicIntegral

/-- Le paquet de référence porte bien l’intégralité finie documentaire. -/
theorem couretQuadraticIntegralReferencePackage_documentaryIntegral :
    hasIntegralSpectrum
      couretQuadraticIntegralReferencePackage.interface.quadratic.candidate.documentary.candidate := by
  exact couretQuadraticIntegralReferencePackage.interface.documentaryIntegral

/--
Validation groupée de l’objet compact canonique quadratique intégral
de référence du cas Couret :
- recollement harmonique/documentaire historique,
- réalisation quadratique harmonique,
- recollement quadratique harmonique/documentaire,
- intégralité harmonique minimale,
- intégralité finie documentaire.
-/
theorem couretQuadraticIntegralReferencePackage_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretQuadraticIntegralReferencePackage.interface.quadratic.candidate.documentary.candidate
      ∧ couretQuadraticIntegralReferencePackage.interface.quadratic.powerCoeffs =
          tripletPowerSpectrum couretTriplet
      ∧ couretQuadraticIntegralReferencePackage.interface.quadratic.powerCoeffs =
          couretQuadraticIntegralReferencePackage.interface.quadratic.candidate.documentary.candidate.powerHistorical.map
            (fun n => (n : ℝ))
      ∧ certificateHasIntegralEntries
          couretQuadraticIntegralReferencePackage.interface.quadratic.candidate.documentary.harmonic
      ∧ hasIntegralSpectrum
          couretQuadraticIntegralReferencePackage.interface.quadratic.candidate.documentary.candidate := by
  exact ⟨ couretQuadraticIntegralReferencePackage_matchesHistorical
        , couretQuadraticIntegralReferencePackage_realizesPower
        , couretQuadraticIntegralReferencePackage_matchesHistoricalPower
        , couretQuadraticIntegralReferencePackage_harmonicIntegral
        , couretQuadraticIntegralReferencePackage_documentaryIntegral ⟩

end

end CouretUnification.Core