import CouretUnification.Core.TripletExceptionalPredicate
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Enveloppe décidable purement locale autour du prédicat
`isLocalExceptionalCandidate`.

On ne décide ici qu’un prédicat local déjà isolé ;
on ne filtre encore aucun triplet
et on n’ouvre pas `ExceptionalFilter`.
-/
structure TripletExceptionalDecidableShell (T : Triplet) where
  predicate : Prop
  predicate_eq : predicate = isLocalExceptionalCandidate T
  decidablePredicate : Decidable predicate

/--
Shell canonique : on prend exactement le prédicat local déjà défini,
muni de sa décidabilité classique.
-/
def canonicalTripletExceptionalDecidableShell
    (T : Triplet) : TripletExceptionalDecidableShell T where
  predicate := isLocalExceptionalCandidate T
  predicate_eq := rfl
  decidablePredicate := by
    classical
    infer_instance

/--
Le shell empaqueté porte bien exactement le prédicat local attendu.
-/
theorem TripletExceptionalDecidableShell.predicate_isLocalExceptionalCandidate
    {T : Triplet} (S : TripletExceptionalDecidableShell T) :
    S.predicate = isLocalExceptionalCandidate T := by
  exact S.predicate_eq

/--
Version calculatoire : la décidabilité locale du prédicat.
Ce n’est pas un théorème, mais une donnée.
-/
def canonicalTripletExceptionalDecidable
    (T : Triplet) :
    Decidable (isLocalExceptionalCandidate T) := by
  classical
  simpa [canonicalTripletExceptionalDecidableShell] using
    (canonicalTripletExceptionalDecidableShell T).decidablePredicate

/--
Cas Couret : shell décidable canonique.
-/
def couretTripletExceptionalDecidableShell :
    TripletExceptionalDecidableShell couretTriplet :=
  canonicalTripletExceptionalDecidableShell couretTriplet

/--
Dans le cas Couret, le prédicat empaqueté est bien vrai.
-/
theorem couretTripletExceptionalDecidableShell_true :
    couretTripletExceptionalDecidableShell.predicate := by
  simpa [couretTripletExceptionalDecidableShell,
    canonicalTripletExceptionalDecidableShell] using
    couretTriplet_isLocalExceptionalCandidate

/--
Version calculatoire spécialisée au cas Couret.
-/
def couretTripletExceptionalDecidable :
    Decidable couretTripletExceptionalDecidableShell.predicate :=
  couretTripletExceptionalDecidableShell.decidablePredicate

/--
Validation minimale du cas Couret au niveau de la shell :
le prédicat local empaqueté est vrai.
-/
theorem couretTripletExceptionalDecidableShell_valid :
    couretTripletExceptionalDecidableShell.predicate := by
  exact couretTripletExceptionalDecidableShell_true

end

end CouretUnification.Core