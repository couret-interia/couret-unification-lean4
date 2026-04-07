import CouretUnification.Core.CouretDocumentaryCertificate
import CouretUnification.Core.TripletPowerSpectrum
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Certificat quadratique compact du seul cas Couret :
- certificat documentaire compact,
- recollement du profil quadratique harmonique historique.
-/
structure CouretPowerCertificate where
  documentary : CouretDocumentaryCertificate
  powerHistorical :
    matchesHistoricalPowerSpectrum couretTriplet

/-- Certificat quadratique canonique du cas Couret. -/
def couretPowerCertificate : CouretPowerCertificate where
  documentary := couretDocumentaryCertificate
  powerHistorical := couretTriplet_matchesHistoricalPowerSpectrum

/-- Le certificat quadratique compact porte bien le recollement historique quadratique. -/
theorem couretPowerCertificate_matchesHistorical :
    matchesHistoricalPowerSpectrum couretTriplet := by
  exact couretPowerCertificate.powerHistorical

/--
Le profil quadratique harmonique calculé recolle bien avec le profil
quadratique documentaire historique du spectre gelé de Couret.
-/
theorem couretPowerCertificate_reconstructs_finiteSpectrum :
    tripletPowerSpectrum couretTriplet =
      couretTripletSpectrum.powerHistorical.map (fun n => (n : ℝ)) := by
  simpa using couretTriplet_power_reconstructs_finiteSpectrum

/--
Le certificat quadratique compact reste adossé au certificat documentaire
canonique du cas Couret.
-/
theorem couretPowerCertificate_documentary :
    couretPowerCertificate.documentary = couretDocumentaryCertificate := by
  rfl

/--
Le certificat quadratique compact conserve l'intégralité finie documentaire.
-/
theorem couretPowerCertificate_hasFiniteIntegral :
    hasIntegralSpectrum couretTripletSpectrum := by
  exact couretPowerCertificate.documentary.finiteIntegral

/--
Validation groupée du certificat quadratique de Couret :
- recollement quadratique harmonique historique,
- recollement avec le `FiniteSpectrum` documentaire,
- intégralité finie documentaire.
-/
theorem couretPowerCertificate_valid :
    matchesHistoricalPowerSpectrum couretTriplet
      ∧ tripletPowerSpectrum couretTriplet =
          couretTripletSpectrum.powerHistorical.map (fun n => (n : ℝ))
      ∧ hasIntegralSpectrum couretTripletSpectrum := by
  exact ⟨ couretPowerCertificate_matchesHistorical
        , couretPowerCertificate_reconstructs_finiteSpectrum
        , couretPowerCertificate_hasFiniteIntegral ⟩

end

end CouretUnification.Core