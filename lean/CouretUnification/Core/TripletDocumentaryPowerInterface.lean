import CouretUnification.Core.TripletDocumentaryCertificate
import CouretUnification.Core.TripletPowerSpectrum
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Interface minimale entre :
- un certificat documentaire candidat pour un triplet arbitraire,
- et son profil quadratique harmonique calculé.

On ne filtre encore aucun triplet,
et on n’ouvre pas `ExceptionalFilter`.
-/
structure TripletDocumentaryPowerInterface (T : Triplet) where
  documentary : TripletDocumentaryCertificate T
  powerHistoricalRecollement :
    tripletPowerSpectrum T =
      documentary.candidate.powerHistorical.map (fun n => (n : ℝ))

/--
Constructeur minimal :
on empaquette un certificat documentaire déjà construit
avec le recollement quadratique harmonique/documentaire correspondant.
-/
def mkTripletDocumentaryPowerInterface
    (T : Triplet)
    (D : TripletDocumentaryCertificate T)
    (hP :
      tripletPowerSpectrum T =
        D.candidate.powerHistorical.map (fun n => (n : ℝ))) :
    TripletDocumentaryPowerInterface T where
  documentary := D
  powerHistoricalRecollement := hP

/--
L’interface empaquetée conserve bien le recollement historique harmonique/documentaire.
-/
theorem TripletDocumentaryPowerInterface.matchesHistorical
    {T : Triplet} (I : TripletDocumentaryPowerInterface T) :
    matchesHistoricalSpectrum T I.documentary.candidate := by
  exact I.documentary.matchesHistorical

/--
L’interface empaquetée porte bien le recollement quadratique harmonique/documentaire
vers le candidat documentaire.
-/
theorem TripletDocumentaryPowerInterface.matchesHistoricalPower
    {T : Triplet} (I : TripletDocumentaryPowerInterface T) :
    tripletPowerSpectrum T =
      I.documentary.candidate.powerHistorical.map (fun n => (n : ℝ)) := by
  exact I.powerHistoricalRecollement

/--
Prédicat brut : un certificat documentaire recolle quadratiquement
avec son candidat documentaire.
-/
def documentaryCertificateMatchesHistoricalPower
    {T : Triplet} (D : TripletDocumentaryCertificate T) : Prop :=
  tripletPowerSpectrum T =
    D.candidate.powerHistorical.map (fun n => (n : ℝ))

/--
Cas Couret : interface canonique harmonique/documentaire/quadratique.
-/
def couretTripletDocumentaryPowerInterface :
    TripletDocumentaryPowerInterface couretTriplet :=
  mkTripletDocumentaryPowerInterface
    couretTriplet
    couretTripletDocumentaryCertificate
    couretTriplet_power_reconstructs_finiteSpectrum

/--
Validation groupée du cas Couret :
- recollement harmonique/documentaire historique,
- recollement quadratique harmonique/documentaire vers le candidat gelé.
-/
theorem couretTripletDocumentaryPowerInterface_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretTripletDocumentaryPowerInterface.documentary.candidate
      ∧ tripletPowerSpectrum couretTriplet =
          couretTripletDocumentaryPowerInterface.documentary.candidate.powerHistorical.map
            (fun n => (n : ℝ)) := by
  exact ⟨ couretTripletDocumentaryPowerInterface.matchesHistorical
        , couretTripletDocumentaryPowerInterface.matchesHistoricalPower ⟩

end

end CouretUnification.Core