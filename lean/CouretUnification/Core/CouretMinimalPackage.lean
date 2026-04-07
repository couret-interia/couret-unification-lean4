import CouretUnification.Core.CouretPowerCertificate
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet minimal compact de référence du seul cas Couret :
- certificat harmonique canonique,
- certificat documentaire compact,
- certificat quadratique compact,
- intégralité finie documentaire.
-/
structure CouretMinimalPackage where
  harmonic : HarmonicCertificate couretTriplet
  documentary : CouretDocumentaryCertificate
  power : CouretPowerCertificate
  finiteIntegral : hasIntegralSpectrum couretTripletSpectrum

/-- Paquet minimal canonique du cas Couret. -/
def couretMinimalPackage : CouretMinimalPackage where
  harmonic := canonicalHarmonicCertificate couretTriplet
  documentary := couretDocumentaryCertificate
  power := couretPowerCertificate
  finiteIntegral := couretTriplet_hasIntegralSpectrum

/-- La composante harmonique est bien le certificat canonique du cas Couret. -/
theorem couretMinimalPackage_harmonic :
    couretMinimalPackage.harmonic =
      canonicalHarmonicCertificate couretTriplet := by
  rfl

/-- La composante documentaire est bien le certificat documentaire compact canonique. -/
theorem couretMinimalPackage_documentary :
    couretMinimalPackage.documentary =
      couretDocumentaryCertificate := by
  rfl

/-- La composante quadratique est bien le certificat quadratique compact canonique. -/
theorem couretMinimalPackage_power :
    couretMinimalPackage.power =
      couretPowerCertificate := by
  rfl

/-- La composante harmonique recolle bien avec le spectre historique documentaire gelé. -/
theorem couretMinimalPackage_matchesHistorical :
    certificateMatchesHistoricalSpectrum
      couretMinimalPackage.harmonic
      couretTripletSpectrum := by
  simpa [couretMinimalPackage]
    using couretCanonicalCertificate_matchesHistorical

/-- La composante harmonique a bien des entrées entières. -/
theorem couretMinimalPackage_harmonicEntriesIntegral :
    certificateHasIntegralEntries
      couretMinimalPackage.harmonic := by
  simpa [couretMinimalPackage]
    using couretCanonicalCertificate_hasIntegralEntries

/-- La composante documentaire compacte recolle bien avec l'historique. -/
theorem couretMinimalPackage_documentaryMatchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretMinimalPackage.documentary.documentary.candidate := by
  simpa [couretMinimalPackage]
    using couretDocumentaryCertificate_matchesHistorical

/-- La composante quadratique compacte recolle bien avec le profil historique. -/
theorem couretMinimalPackage_powerMatchesHistorical :
    matchesHistoricalPowerSpectrum couretTriplet := by
  simpa [couretMinimalPackage]
    using couretPowerCertificate_matchesHistorical

/-- La composante quadratique recolle bien avec le `FiniteSpectrum` documentaire gelé. -/
theorem couretMinimalPackage_powerReconstructsFiniteSpectrum :
    tripletPowerSpectrum couretTriplet =
      couretTripletSpectrum.powerHistorical.map (fun n => (n : ℝ)) := by
  simpa [couretMinimalPackage]
    using couretPowerCertificate_reconstructs_finiteSpectrum

/-- Le paquet minimal conserve bien l'intégralité finie documentaire. -/
theorem couretMinimalPackage_hasFiniteIntegral :
    hasIntegralSpectrum couretTripletSpectrum := by
  exact couretMinimalPackage.finiteIntegral

/--
Validation groupée du paquet minimal du cas Couret :
- recollement harmonique/documentaire historique,
- intégralité harmonique,
- recollement quadratique historique,
- recollement quadratique avec le `FiniteSpectrum`,
- intégralité finie documentaire.
-/
theorem couretMinimalPackage_valid :
    certificateMatchesHistoricalSpectrum
        couretMinimalPackage.harmonic
        couretTripletSpectrum
      ∧ certificateHasIntegralEntries
          couretMinimalPackage.harmonic
      ∧ matchesHistoricalPowerSpectrum couretTriplet
      ∧ tripletPowerSpectrum couretTriplet =
          couretTripletSpectrum.powerHistorical.map (fun n => (n : ℝ))
      ∧ hasIntegralSpectrum couretTripletSpectrum := by
  exact ⟨ couretMinimalPackage_matchesHistorical
        , couretMinimalPackage_harmonicEntriesIntegral
        , couretMinimalPackage_powerMatchesHistorical
        , couretMinimalPackage_powerReconstructsFiniteSpectrum
        , couretMinimalPackage_hasFiniteIntegral ⟩

end

end CouretUnification.Core