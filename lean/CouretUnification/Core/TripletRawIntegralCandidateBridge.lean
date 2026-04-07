import CouretUnification.Core.TripletCandidateInterface
import CouretUnification.Core.TripletRawIntegralCriterion
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Pont minimal, pour un triplet arbitraire, entre :
- un candidat documentaire harmonico-quadratique,
- un critère brut d’intégralité harmonique.

On impose seulement ici que les deux couches utilisent bien
le même certificat harmonique canonique.
-/
structure TripletRawIntegralCandidateBridge (T : Triplet) where
  candidate : TripletCandidateInterface T
  rawCriterion : TripletRawIntegralCriterion T
  harmonicCompatibility :
    candidate.documentary.harmonic = rawCriterion.harmonic

/--
Constructeur minimal :
à partir d’un candidat harmonico-quadratique déjà construit
et d’un critère brut d’intégralité déjà construit,
on les relie par compatibilité harmonique.
-/
def mkTripletRawIntegralCandidateBridge
    (T : Triplet)
    (C : TripletCandidateInterface T)
    (R : TripletRawIntegralCriterion T)
    (hCompat : C.documentary.harmonic = R.harmonic) :
    TripletRawIntegralCandidateBridge T where
  candidate := C
  rawCriterion := R
  harmonicCompatibility := hCompat

/--
Le pont empaqueté conserve bien le recollement historique
harmonique/documentaire du candidat.
-/
theorem TripletRawIntegralCandidateBridge.matchesHistorical
    {T : Triplet} (B : TripletRawIntegralCandidateBridge T) :
    matchesHistoricalSpectrum T B.candidate.documentary.candidate := by
  exact B.candidate.matchesHistorical

/--
Le pont empaqueté conserve bien le recollement quadratique
harmonique/documentaire du candidat.
-/
theorem TripletRawIntegralCandidateBridge.matchesHistoricalPower
    {T : Triplet} (B : TripletRawIntegralCandidateBridge T) :
    tripletPowerSpectrum T =
      B.candidate.documentary.candidate.powerHistorical.map (fun n => (n : ℝ)) := by
  exact B.candidate.matchesHistoricalPower

/--
Le pont empaqueté conserve bien le critère brut d’intégralité harmonique.
-/
theorem TripletRawIntegralCandidateBridge.rawIntegral
    {T : Triplet} (B : TripletRawIntegralCandidateBridge T) :
    hasRawIntegralCriterion T := by
  exact B.rawCriterion.raw

/--
Le pont empaqueté identifie bien les deux certificats harmoniques sous-jacents.
-/
theorem TripletRawIntegralCandidateBridge.harmonic_eq
    {T : Triplet} (B : TripletRawIntegralCandidateBridge T) :
    B.candidate.documentary.harmonic = B.rawCriterion.harmonic := by
  exact B.harmonicCompatibility

/--
Le pont empaqueté réalise bien le calcul harmonique canonique
via son critère brut.
-/
theorem TripletRawIntegralCandidateBridge.realizes
    {T : Triplet} (B : TripletRawIntegralCandidateBridge T) :
    tripletFourier T = B.rawCriterion.harmonic.coeffs := by
  exact B.rawCriterion.realizes

/--
Cas Couret : pont canonique entre
- le candidat documentaire harmonico-quadratique canonique,
- et le critère brut d’intégralité canonique.
-/
def couretTripletRawIntegralCandidateBridge :
    TripletRawIntegralCandidateBridge couretTriplet :=
  mkTripletRawIntegralCandidateBridge
    couretTriplet
    couretTripletCandidateInterface
    couretTripletRawIntegralCriterion
    (by rfl)

/--
Dans le cas Couret, le pont recolle bien avec l’historique documentaire.
-/
theorem couretTripletRawIntegralCandidateBridge_matchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretTripletRawIntegralCandidateBridge.candidate.documentary.candidate := by
  exact couretTripletRawIntegralCandidateBridge.matchesHistorical

/--
Dans le cas Couret, le pont recolle bien quadratiquement
avec l’historique documentaire.
-/
theorem couretTripletRawIntegralCandidateBridge_matchesHistoricalPower :
    tripletPowerSpectrum couretTriplet =
      couretTripletRawIntegralCandidateBridge.candidate.documentary.candidate.powerHistorical.map
        (fun n => (n : ℝ)) := by
  exact couretTripletRawIntegralCandidateBridge.matchesHistoricalPower

/--
Dans le cas Couret, le critère brut d’intégralité est bien satisfait.
-/
theorem couretTripletRawIntegralCandidateBridge_rawIntegral :
    hasRawIntegralCriterion couretTriplet := by
  exact couretTripletRawIntegralCandidateBridge.rawIntegral

/--
Dans le cas Couret, les deux certificats harmoniques coïncident bien.
-/
theorem couretTripletRawIntegralCandidateBridge_harmonic_eq :
    couretTripletRawIntegralCandidateBridge.candidate.documentary.harmonic =
      couretTripletRawIntegralCandidateBridge.rawCriterion.harmonic := by
  exact couretTripletRawIntegralCandidateBridge.harmonic_eq

/--
Validation groupée du cas Couret :
- recollement harmonique/documentaire historique,
- recollement quadratique harmonique/documentaire,
- critère brut d’intégralité harmonique,
- compatibilité harmonique entre les deux couches empaquetées.
-/
theorem couretTripletRawIntegralCandidateBridge_valid :
    matchesHistoricalSpectrum
        couretTriplet
        couretTripletRawIntegralCandidateBridge.candidate.documentary.candidate
      ∧ tripletPowerSpectrum couretTriplet =
          couretTripletRawIntegralCandidateBridge.candidate.documentary.candidate.powerHistorical.map
            (fun n => (n : ℝ))
      ∧ hasRawIntegralCriterion couretTriplet
      ∧ couretTripletRawIntegralCandidateBridge.candidate.documentary.harmonic =
          couretTripletRawIntegralCandidateBridge.rawCriterion.harmonic := by
  exact ⟨ couretTripletRawIntegralCandidateBridge_matchesHistorical
        , couretTripletRawIntegralCandidateBridge_matchesHistoricalPower
        , couretTripletRawIntegralCandidateBridge_rawIntegral
        , couretTripletRawIntegralCandidateBridge_harmonic_eq ⟩

end

end CouretUnification.Core