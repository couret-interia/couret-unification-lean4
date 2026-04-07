import CouretUnification.Core.TripletDocumentaryCertificate
import CouretUnification.Core.IntegralSpectrum
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Certificat documentaire compact de référence pour le seul cas Couret :
- certificat documentaire harmonique,
- intégralité harmonique,
- intégralité finie documentaire.
-/
structure CouretDocumentaryCertificate where
  documentary :
    TripletDocumentaryCertificate couretTriplet
  harmonicIntegral :
    hasIntegralHarmonicSpectrum couretTriplet
  finiteIntegral :
    hasIntegralSpectrum couretTripletSpectrum

/-- Certificat documentaire canonique du cas Couret. -/
def couretDocumentaryCertificate : CouretDocumentaryCertificate where
  documentary := couretTripletDocumentaryCertificate
  harmonicIntegral := couretTriplet_hasIntegralHarmonicSpectrum
  finiteIntegral := couretTriplet_hasIntegralSpectrum

/-- Le certificat documentaire compact recolle bien avec l'historique. -/
theorem couretDocumentaryCertificate_matchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretDocumentaryCertificate.documentary.candidate := by
  exact couretTripletDocumentaryCertificate_matchesHistorical

/-- Le candidat documentaire empaqueté est exactement le spectre gelé de Couret. -/
theorem couretDocumentaryCertificate_candidate :
    couretDocumentaryCertificate.documentary.candidate = couretTripletSpectrum := by
  rfl

/-- Le certificat harmonique empaqueté est le certificat canonique du cas Couret. -/
theorem couretDocumentaryCertificate_harmonic :
    couretDocumentaryCertificate.documentary.harmonic =
      canonicalHarmonicCertificate couretTriplet := by
  rfl

/-- Le certificat documentaire compact porte bien l'intégralité harmonique. -/
theorem couretDocumentaryCertificate_hasHarmonicIntegral :
    hasIntegralHarmonicSpectrum couretTriplet := by
  exact couretDocumentaryCertificate.harmonicIntegral

/-- Le certificat documentaire compact porte bien l'intégralité finie. -/
theorem couretDocumentaryCertificate_hasFiniteIntegral :
    hasIntegralSpectrum couretTripletSpectrum := by
  exact couretDocumentaryCertificate.finiteIntegral

/--
Formulation groupée compacte :
- recollement harmonique/documentaire,
- intégralité harmonique,
- intégralité finie.
-/
theorem couretDocumentaryCertificate_valid :
    matchesHistoricalSpectrum couretTriplet couretTripletSpectrum
      ∧ hasIntegralHarmonicSpectrum couretTriplet
      ∧ hasIntegralSpectrum couretTripletSpectrum := by
  exact ⟨ by simpa [couretDocumentaryCertificate_candidate]
            using couretDocumentaryCertificate_matchesHistorical
        , couretDocumentaryCertificate_hasHarmonicIntegral
        , couretDocumentaryCertificate_hasFiniteIntegral ⟩

end

end CouretUnification.Core