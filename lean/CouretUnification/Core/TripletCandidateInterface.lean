import CouretUnification.Core.TripletDocumentaryCertificate
import CouretUnification.Core.TripletPowerSpectrum
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Interface minimale de candidat documentaire harmonico-quadratique
pour un triplet arbitraire :
- un certificat documentaire candidat,
- un recollement quadratique harmonique/documentaire
  vers le profil quadratique historique du candidat.

Aucune intégralité n'est encore imposée ici.
Aucun filtrage global n'est encore ouvert.
-/
structure TripletCandidateInterface (T : Triplet) where
  documentary : TripletDocumentaryCertificate T
  powerHistoricalRecollement :
    tripletPowerSpectrum T =
      documentary.candidate.powerHistorical.map (fun n => (n : ℝ))

/--
Constructeur minimal :
on empaquette un certificat documentaire déjà construit
avec son recollement quadratique harmonique/documentaire.
-/
def mkTripletCandidateInterface
    (T : Triplet)
    (D : TripletDocumentaryCertificate T)
    (hP :
      tripletPowerSpectrum T =
        D.candidate.powerHistorical.map (fun n => (n : ℝ))) :
    TripletCandidateInterface T where
  documentary := D
  powerHistoricalRecollement := hP

/--
Le candidat empaqueté conserve bien le recollement historique
harmonique/documentaire.
-/
theorem TripletCandidateInterface.matchesHistorical
    {T : Triplet} (C : TripletCandidateInterface T) :
    matchesHistoricalSpectrum T C.documentary.candidate := by
  exact C.documentary.matchesHistorical

/--
Le candidat empaqueté conserve bien le recollement quadratique
harmonique/documentaire.
-/
theorem TripletCandidateInterface.matchesHistoricalPower
    {T : Triplet} (C : TripletCandidateInterface T) :
    tripletPowerSpectrum T =
      C.documentary.candidate.powerHistorical.map (fun n => (n : ℝ)) := by
  exact C.powerHistoricalRecollement

/--
Prédicat brut : un certificat documentaire porte un candidat quadratique
cohérent avec le calcul harmonique.
-/
def documentaryCertificateMatchesHistoricalPower
    {T : Triplet} (D : TripletDocumentaryCertificate T) : Prop :=
  tripletPowerSpectrum T =
    D.candidate.powerHistorical.map (fun n => (n : ℝ))

/--
Cas Couret : candidat documentaire harmonico-quadratique canonique.
-/
def couretTripletCandidateInterface :
    TripletCandidateInterface couretTriplet :=
  mkTripletCandidateInterface
    couretTriplet
    couretTripletDocumentaryCertificate
    couretTriplet_power_reconstructs_finiteSpectrum

/--
Validation groupée du cas Couret :
- recollement harmonique/documentaire historique,
- recollement quadratique harmonique/documentaire.
-/
theorem couretTripletCandidateInterface_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretTripletCandidateInterface.documentary.candidate
      ∧ tripletPowerSpectrum couretTriplet =
          couretTripletCandidateInterface.documentary.candidate.powerHistorical.map
            (fun n => (n : ℝ)) := by
  exact ⟨ couretTripletCandidateInterface.matchesHistorical
        , couretTripletCandidateInterface.matchesHistoricalPower ⟩

end

end CouretUnification.Core