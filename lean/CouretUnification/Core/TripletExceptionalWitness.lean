import CouretUnification.Core.TripletExceptionalDecidableShell
import CouretUnification.Core.TripletExceptionalPredicate
import CouretUnification.Core.TripletLocalExceptionalCandidate
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Témoin local explicite de candidature exceptionnelle, pour un triplet arbitraire :

- une shell décidable locale ;
- une preuve que le prédicat empaqueté dans cette shell est vrai.

On n’ouvre encore :
- aucun filtrage global,
- aucune classification des 21 triplets,
- aucun `ExceptionalFilter`.
-/
structure TripletExceptionalWitness (T : Triplet) where
  shell : TripletExceptionalDecidableShell T
  witnessPredicate : shell.predicate

/--
Constructeur canonique :
à partir d’une preuve du prédicat local,
on fabrique le témoin explicite associé à la shell canonique.
-/
def canonicalTripletExceptionalWitness
    (T : Triplet) (h : isLocalExceptionalCandidate T) :
    TripletExceptionalWitness T where
  shell := canonicalTripletExceptionalDecidableShell T
  witnessPredicate := by
    simpa [canonicalTripletExceptionalDecidableShell] using h

/--
Le témoin empaqueté vérifie bien le prédicat local.
-/
theorem TripletExceptionalWitness.predicate
    {T : Triplet} (W : TripletExceptionalWitness T) :
    isLocalExceptionalCandidate T := by
  simpa [W.shell.predicate_isLocalExceptionalCandidate] using W.witnessPredicate

/--
Le témoin empaqueté fournit bien un candidat local explicite.
-/
def TripletExceptionalWitness.localCandidate
    {T : Triplet} (W : TripletExceptionalWitness T) :
    TripletLocalExceptionalCandidate T :=
  Classical.choice W.predicate

/--
Cas Couret : témoin explicite canonique.
-/
def couretTripletExceptionalWitness :
    TripletExceptionalWitness couretTriplet :=
  canonicalTripletExceptionalWitness
    couretTriplet
    couretTriplet_isLocalExceptionalCandidate

/--
Dans le cas Couret, le témoin explicite vérifie bien le prédicat local.
-/
theorem couretTripletExceptionalWitness_predicate :
    isLocalExceptionalCandidate couretTriplet := by
  exact couretTripletExceptionalWitness.predicate

/--
Validation minimale du cas Couret :
- le témoin explicite existe ;
- il vérifie bien le prédicat local ;
- il fournit donc un candidat local explicite.
-/
theorem couretTripletExceptionalWitness_valid :
    isLocalExceptionalCandidate couretTriplet := by
  exact couretTripletExceptionalWitness_predicate

end

end CouretUnification.Core