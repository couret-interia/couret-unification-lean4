import CouretUnification.Core.TripletCandidateInterface
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Certificat candidat purement quadratique pour un triplet arbitraire :
- un candidat documentaire harmonico-quadratique,
- une liste quadratique de longueur 8,
- la preuve qu'elle réalise exactement `tripletPowerSpectrum T`,
- la preuve qu'elle recolle avec le profil quadratique historique
  du candidat documentaire.

On n'impose encore ici :
- ni intégralité harmonique,
- ni intégralité finie,
- ni filtrage global,
- ni `ExceptionalFilter`.
-/
structure TripletQuadraticCandidateCertificate (T : Triplet) where
  candidate : TripletCandidateInterface T
  powerCoeffs : List ℝ
  powerCoeffs_len : powerCoeffs.length = 8
  realizes :
    powerCoeffs = tripletPowerSpectrum T
  historicalPowerRecollement :
    powerCoeffs =
      candidate.documentary.candidate.powerHistorical.map (fun n => (n : ℝ))

/--
Constructeur canonique :
à partir d'un candidat harmonico-quadratique déjà construit,
on empaquette le certificat purement quadratique correspondant.
-/
def canonicalTripletQuadraticCandidateCertificate
    (T : Triplet)
    (C : TripletCandidateInterface T) :
    TripletQuadraticCandidateCertificate T where
  candidate := C
  powerCoeffs := tripletPowerSpectrum T
  powerCoeffs_len := tripletPowerSpectrum_length T
  realizes := rfl
  historicalPowerRecollement := C.matchesHistoricalPower

/--
Le certificat quadratique empaqueté conserve bien
le recollement historique harmonique/documentaire.
-/
theorem TripletQuadraticCandidateCertificate.matchesHistorical
    {T : Triplet} (Q : TripletQuadraticCandidateCertificate T) :
    matchesHistoricalSpectrum T Q.candidate.documentary.candidate := by
  exact Q.candidate.matchesHistorical

/--
Le certificat quadratique empaqueté réalise bien
le calcul quadratique harmonique canonique.
-/
theorem TripletQuadraticCandidateCertificate.realizesPower
    {T : Triplet} (Q : TripletQuadraticCandidateCertificate T) :
    Q.powerCoeffs = tripletPowerSpectrum T := by
  exact Q.realizes

/--
Le certificat quadratique empaqueté recolle bien
avec le profil quadratique historique du candidat documentaire.
-/
theorem TripletQuadraticCandidateCertificate.matchesHistoricalPower
    {T : Triplet} (Q : TripletQuadraticCandidateCertificate T) :
    Q.powerCoeffs =
      Q.candidate.documentary.candidate.powerHistorical.map (fun n => (n : ℝ)) := by
  exact Q.historicalPowerRecollement

/--
Cas Couret : certificat candidat purement quadratique canonique.
-/
def couretTripletQuadraticCandidateCertificate :
    TripletQuadraticCandidateCertificate couretTriplet :=
  canonicalTripletQuadraticCandidateCertificate
    couretTriplet
    couretTripletCandidateInterface

/--
Validation groupée du cas Couret :
- recollement harmonique/documentaire historique,
- réalisation quadratique harmonique,
- recollement quadratique avec le `FiniteSpectrum` documentaire gelé.
-/
theorem couretTripletQuadraticCandidateCertificate_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretTripletQuadraticCandidateCertificate.candidate.documentary.candidate
      ∧ couretTripletQuadraticCandidateCertificate.powerCoeffs =
          tripletPowerSpectrum couretTriplet
      ∧ couretTripletQuadraticCandidateCertificate.powerCoeffs =
          couretTripletQuadraticCandidateCertificate.candidate.documentary.candidate.powerHistorical.map
            (fun n => (n : ℝ)) := by
  exact ⟨ couretTripletQuadraticCandidateCertificate.matchesHistorical
        , couretTripletQuadraticCandidateCertificate.realizesPower
        , couretTripletQuadraticCandidateCertificate.matchesHistoricalPower ⟩

end

end CouretUnification.Core