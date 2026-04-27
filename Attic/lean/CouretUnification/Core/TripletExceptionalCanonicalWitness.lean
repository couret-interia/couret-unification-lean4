import CouretUnification.Core.TripletExceptionalLocalPackage
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Témoin canonique explicite de candidature exceptionnelle locale,
pour un triplet arbitraire, lorsqu’un paquet local cohérent
est déjà disponible.

On ne filtre encore aucun triplet,
et on n’ouvre pas `ExceptionalFilter`.
-/
def canonicalWitnessFromLocalPackage
    {T : Triplet} (P : TripletExceptionalLocalPackage T) :
    TripletExceptionalWitness T :=
  P.witness

/--
Le témoin canonique extrait du paquet local utilise bien
exactement la shell locale déjà empaquetée.
-/
theorem canonicalWitnessFromLocalPackage_shell
    {T : Triplet} (P : TripletExceptionalLocalPackage T) :
    (canonicalWitnessFromLocalPackage P).shell = P.shell := by
  simpa [canonicalWitnessFromLocalPackage] using P.witnessShell

/--
Le témoin canonique extrait du paquet local vérifie bien
le prédicat local de candidature exceptionnelle.
-/
theorem canonicalWitnessFromLocalPackage_predicate
    {T : Triplet} (P : TripletExceptionalLocalPackage T) :
    isLocalExceptionalCandidate T := by
  exact (canonicalWitnessFromLocalPackage P).predicate

/--
Le candidat local explicite extrait du témoin canonique
coïncide bien avec celui déjà porté par le paquet local.
-/
theorem canonicalWitnessFromLocalPackage_localCandidate
    {T : Triplet} (P : TripletExceptionalLocalPackage T) :
    (canonicalWitnessFromLocalPackage P).localCandidate = P.localCandidate := by
  rfl

/--
Le témoin canonique extrait du paquet local conserve bien
le recollement harmonique/documentaire historique.
-/
theorem canonicalWitnessFromLocalPackage_matchesHistorical
    {T : Triplet} (P : TripletExceptionalLocalPackage T) :
    matchesHistoricalSpectrum
      T
      (canonicalWitnessFromLocalPackage P).localCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate := by
  simpa [canonicalWitnessFromLocalPackage_localCandidate] using P.matchesHistorical

/--
Cas Couret : témoin canonique explicite extrait du paquet local canonique.
-/
def couretTripletExceptionalCanonicalWitness :
    TripletExceptionalWitness couretTriplet :=
  canonicalWitnessFromLocalPackage couretTripletExceptionalLocalPackage

/--
Dans le cas Couret, le témoin canonique explicite vérifie bien
le prédicat local.
-/
theorem couretTripletExceptionalCanonicalWitness_predicate :
    isLocalExceptionalCandidate couretTriplet := by
  exact couretTripletExceptionalCanonicalWitness.predicate

/--
Dans le cas Couret, le témoin canonique explicite utilise bien
la shell locale canonique déjà empaquetée.
-/
theorem couretTripletExceptionalCanonicalWitness_shell :
    couretTripletExceptionalCanonicalWitness.shell =
      couretTripletExceptionalLocalPackage.shell := by
  exact canonicalWitnessFromLocalPackage_shell couretTripletExceptionalLocalPackage

/--
Dans le cas Couret, le témoin canonique explicite conserve bien
le recollement historique documentaire.
-/
theorem couretTripletExceptionalCanonicalWitness_matchesHistorical :
    matchesHistoricalSpectrum
      couretTriplet
      couretTripletExceptionalCanonicalWitness.localCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate := by
  exact canonicalWitnessFromLocalPackage_matchesHistorical
    couretTripletExceptionalLocalPackage

/--
Validation minimale du cas Couret :
- le témoin canonique explicite vérifie le prédicat local ;
- il reste adossé à la shell locale empaquetée ;
- il conserve le recollement historique documentaire.
-/
theorem couretTripletExceptionalCanonicalWitness_valid :
    isLocalExceptionalCandidate couretTriplet
      ∧ couretTripletExceptionalCanonicalWitness.shell =
          couretTripletExceptionalLocalPackage.shell
      ∧ matchesHistoricalSpectrum
          couretTriplet
          couretTripletExceptionalCanonicalWitness.localCandidate.quadraticIntegral.quadratic.candidate.documentary.candidate := by
  exact ⟨ couretTripletExceptionalCanonicalWitness_predicate
        , couretTripletExceptionalCanonicalWitness_shell
        , couretTripletExceptionalCanonicalWitness_matchesHistorical ⟩

end

end CouretUnification.Core