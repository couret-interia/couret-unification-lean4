import CouretUnification.Core.TripletExceptionalCanonicalWitness
import CouretUnification.Core.TripletExceptionalCoreView
import CouretUnification.Core.TripletExceptionalLocalCriterion
import CouretUnification.Core.TripletExceptionalLocalSummary
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Pont canonique, pour un triplet arbitraire, entre :

- le témoin canonique explicite de candidature exceptionnelle locale ;
- la vue noyau locale unifiée ;
- le critère local synthétique.

On ne filtre encore aucun triplet,
et on n’ouvre pas `ExceptionalFilter`.
-/
structure TripletExceptionalCanonicalBridge (T : Triplet) where
  witness : TripletExceptionalWitness T
  coreView : TripletExceptionalCoreView T
  criterion : satisfiesExceptionalLocalCriterion T
  localCompatibility :
    witness.localCandidate = coreView.localPackage.localCandidate

/--
Constructeur canonique :
à partir d’un paquet local déjà construit,
on relie proprement :
- le témoin canonique explicite,
- la vue noyau locale,
- le critère local synthétique.
-/
def canonicalTripletExceptionalCanonicalBridge
    (T : Triplet) (P : TripletExceptionalLocalPackage T) :
    TripletExceptionalCanonicalBridge T where
  witness := canonicalWitnessFromLocalPackage P
  coreView := canonicalTripletExceptionalCoreView T P
  criterion := by
    exact
      TripletExceptionalLocalSummary.satisfiesCriterion
        (canonicalTripletExceptionalLocalSummary
          T
          (canonicalTripletExceptionalCoreView T P))
  localCompatibility := rfl

/--
Le pont canonique empaqueté vérifie bien le prédicat local
de candidature exceptionnelle.
-/
theorem TripletExceptionalCanonicalBridge.predicate
    {T : Triplet} (B : TripletExceptionalCanonicalBridge T) :
    isLocalExceptionalCandidate T := by
  exact B.witness.predicate

/--
Le pont canonique empaqueté conserve bien le recollement historique
harmonique/documentaire.
-/
theorem TripletExceptionalCanonicalBridge.matchesHistorical
    {T : Triplet} (B : TripletExceptionalCanonicalBridge T) :
    matchesHistoricalSpectrum T B.coreView.candidate := by
  exact B.coreView.historicalRecollement

/--
Le pont canonique empaqueté réalise bien le calcul harmonique canonique.
-/
theorem TripletExceptionalCanonicalBridge.harmonicRealizes
    {T : Triplet} (B : TripletExceptionalCanonicalBridge T) :
    tripletFourier T = B.coreView.harmonic.coeffs := by
  exact B.coreView.harmonicRealizes

/--
Le pont canonique empaqueté réalise bien le calcul quadratique harmonique.
-/
theorem TripletExceptionalCanonicalBridge.powerRealizes
    {T : Triplet} (B : TripletExceptionalCanonicalBridge T) :
    B.coreView.powerCoeffs = tripletPowerSpectrum T := by
  exact B.coreView.powerRealizes

/--
Le pont canonique empaqueté conserve bien le recollement quadratique
harmonique/documentaire.
-/
theorem TripletExceptionalCanonicalBridge.matchesHistoricalPower
    {T : Triplet} (B : TripletExceptionalCanonicalBridge T) :
    B.coreView.powerCoeffs =
      B.coreView.candidate.powerHistorical.map (fun n => (n : ℝ)) := by
  exact B.coreView.powerHistoricalRecollement

/--
Le pont canonique empaqueté porte bien l’intégralité harmonique minimale.
-/
theorem TripletExceptionalCanonicalBridge.harmonicIntegral
    {T : Triplet} (B : TripletExceptionalCanonicalBridge T) :
    certificateHasIntegralEntries B.coreView.harmonic := by
  exact B.coreView.harmonicEntriesIntegral

/--
Le pont canonique empaqueté porte bien l’intégralité finie documentaire.
-/
theorem TripletExceptionalCanonicalBridge.finiteIntegral
    {T : Triplet} (B : TripletExceptionalCanonicalBridge T) :
    hasIntegralSpectrum B.coreView.candidate := by
  exact B.coreView.finiteIntegral

/--
Le pont canonique empaqueté porte bien le critère brut d’intégralité harmonique.
-/
theorem TripletExceptionalCanonicalBridge.rawIntegral
    {T : Triplet} (B : TripletExceptionalCanonicalBridge T) :
    hasRawIntegralCriterion T := by
  exact B.coreView.rawIntegral

/--
Le pont canonique empaqueté porte bien le critère local synthétique.
-/
theorem TripletExceptionalCanonicalBridge.satisfiesCriterion
    {T : Triplet} (B : TripletExceptionalCanonicalBridge T) :
    satisfiesExceptionalLocalCriterion T := by
  exact B.criterion

/--
Le pont canonique empaqueté identifie bien
le candidat local du témoin explicite et celui de la vue noyau.
-/
theorem TripletExceptionalCanonicalBridge.localCandidate_eq
    {T : Triplet} (B : TripletExceptionalCanonicalBridge T) :
    B.witness.localCandidate = B.coreView.localPackage.localCandidate := by
  exact B.localCompatibility

/--
Cas Couret : pont canonique explicite de référence.
-/
def couretTripletExceptionalCanonicalBridge :
    TripletExceptionalCanonicalBridge couretTriplet :=
  canonicalTripletExceptionalCanonicalBridge
    couretTriplet
    couretTripletExceptionalLocalPackage

/--
Dans le cas Couret, le pont canonique explicite vérifie bien
le prédicat local.
-/
theorem couretTripletExceptionalCanonicalBridge_predicate :
    isLocalExceptionalCandidate couretTriplet := by
  exact couretTripletExceptionalCanonicalBridge.predicate

/--
Dans le cas Couret, le pont canonique explicite recolle bien
avec l’historique documentaire.
-/
theorem couretTripletExceptionalCanonicalBridge_matchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretTripletExceptionalCanonicalBridge.coreView.candidate := by
  exact couretTripletExceptionalCanonicalBridge.matchesHistorical

/--
Dans le cas Couret, le pont canonique explicite réalise bien
le calcul quadratique harmonique.
-/
theorem couretTripletExceptionalCanonicalBridge_powerRealizes :
    couretTripletExceptionalCanonicalBridge.coreView.powerCoeffs =
      tripletPowerSpectrum couretTriplet := by
  exact couretTripletExceptionalCanonicalBridge.powerRealizes

/--
Dans le cas Couret, le pont canonique explicite recolle bien quadratiquement
avec l’historique documentaire.
-/
theorem couretTripletExceptionalCanonicalBridge_matchesHistoricalPower :
    couretTripletExceptionalCanonicalBridge.coreView.powerCoeffs =
      couretTripletExceptionalCanonicalBridge.coreView.candidate.powerHistorical.map
        (fun n => (n : ℝ)) := by
  exact couretTripletExceptionalCanonicalBridge.matchesHistoricalPower

/--
Dans le cas Couret, le pont canonique explicite porte bien
l’intégralité harmonique minimale.
-/
theorem couretTripletExceptionalCanonicalBridge_harmonicIntegral :
    certificateHasIntegralEntries
      couretTripletExceptionalCanonicalBridge.coreView.harmonic := by
  exact couretTripletExceptionalCanonicalBridge.harmonicIntegral

/--
Dans le cas Couret, le pont canonique explicite porte bien
l’intégralité finie documentaire.
-/
theorem couretTripletExceptionalCanonicalBridge_finiteIntegral :
    hasIntegralSpectrum
      couretTripletExceptionalCanonicalBridge.coreView.candidate := by
  exact couretTripletExceptionalCanonicalBridge.finiteIntegral

/--
Dans le cas Couret, le pont canonique explicite porte bien
le critère brut d’intégralité harmonique.
-/
theorem couretTripletExceptionalCanonicalBridge_rawIntegral :
    hasRawIntegralCriterion couretTriplet := by
  exact couretTripletExceptionalCanonicalBridge.rawIntegral

/--
Dans le cas Couret, le pont canonique explicite porte bien
le critère local synthétique.
-/
theorem couretTripletExceptionalCanonicalBridge_satisfiesCriterion :
    satisfiesExceptionalLocalCriterion couretTriplet := by
  exact couretTripletExceptionalCanonicalBridge.satisfiesCriterion

/--
Dans le cas Couret, le témoin explicite et la vue noyau
portent bien le même candidat local.
-/
theorem couretTripletExceptionalCanonicalBridge_localCandidate_eq :
    couretTripletExceptionalCanonicalBridge.witness.localCandidate =
      couretTripletExceptionalCanonicalBridge.coreView.localPackage.localCandidate := by
  exact couretTripletExceptionalCanonicalBridge.localCandidate_eq

/--
Validation groupée du cas Couret :

- prédicat local ;
- recollement harmonique/documentaire historique ;
- réalisation quadratique harmonique ;
- recollement quadratique harmonique/documentaire ;
- intégralité harmonique minimale ;
- intégralité finie documentaire ;
- critère brut d’intégralité harmonique ;
- critère local synthétique ;
- compatibilité entre témoin canonique et vue noyau.
-/
theorem couretTripletExceptionalCanonicalBridge_valid :
    isLocalExceptionalCandidate couretTriplet
      ∧ matchesHistoricalSpectrum
          couretTriplet
          couretTripletExceptionalCanonicalBridge.coreView.candidate
      ∧ couretTripletExceptionalCanonicalBridge.coreView.powerCoeffs =
          tripletPowerSpectrum couretTriplet
      ∧ couretTripletExceptionalCanonicalBridge.coreView.powerCoeffs =
          couretTripletExceptionalCanonicalBridge.coreView.candidate.powerHistorical.map
            (fun n => (n : ℝ))
      ∧ certificateHasIntegralEntries
          couretTripletExceptionalCanonicalBridge.coreView.harmonic
      ∧ hasIntegralSpectrum
          couretTripletExceptionalCanonicalBridge.coreView.candidate
      ∧ hasRawIntegralCriterion couretTriplet
      ∧ satisfiesExceptionalLocalCriterion couretTriplet
      ∧ couretTripletExceptionalCanonicalBridge.witness.localCandidate =
          couretTripletExceptionalCanonicalBridge.coreView.localPackage.localCandidate := by
  exact ⟨ couretTripletExceptionalCanonicalBridge_predicate
        , couretTripletExceptionalCanonicalBridge_matchesHistorical
        , couretTripletExceptionalCanonicalBridge_powerRealizes
        , couretTripletExceptionalCanonicalBridge_matchesHistoricalPower
        , couretTripletExceptionalCanonicalBridge_harmonicIntegral
        , couretTripletExceptionalCanonicalBridge_finiteIntegral
        , couretTripletExceptionalCanonicalBridge_rawIntegral
        , couretTripletExceptionalCanonicalBridge_satisfiesCriterion
        , couretTripletExceptionalCanonicalBridge_localCandidate_eq ⟩

end

end CouretUnification.Core