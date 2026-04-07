import CouretUnification.Core.ExceptionalLocalCriterionPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Enveloppe décidable purement locale autour du paquet documentaire
du critère local synthétique sur la famille finie des 21 triplets
centrés sur l’identité.

On ne décide ici qu’un prédicat local déjà empaqueté ;
on n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionShell where
  package : IdentityCenteredExceptionalLocalCriterionPackage
  predicate : Prop
  predicate_eq :
    predicate =
      ∀ T : Triplet,
        T ∈ identityCenteredTriplets →
          satisfiesExceptionalLocalPredicateOnIdentityTriplets T →
            ∃ W : IdentityCenteredExceptionalWitness, W.candidate.triplet = T
  decidablePredicate : Decidable predicate

/--
Shell canonique :
on prend le paquet documentaire purement local déjà construit,
et comme prédicat local synthétique global minimal :
tout triplet de la famille identité satisfaisant le critère local
admet un témoin explicite empaqueté.
-/
def identityCenteredExceptionalLocalCriterionShell :
    IdentityCenteredExceptionalLocalCriterionShell where
  package := identityCenteredExceptionalLocalCriterionPackage
  predicate :=
    ∀ T : Triplet,
      T ∈ identityCenteredTriplets →
        satisfiesExceptionalLocalPredicateOnIdentityTriplets T →
          ∃ W : IdentityCenteredExceptionalWitness, W.candidate.triplet = T
  predicate_eq := rfl
  decidablePredicate := by
    classical
    infer_instance

/--
Le shell empaqueté porte bien exactement le prédicat local synthétique global
attendu sur la famille identité.
-/
theorem IdentityCenteredExceptionalLocalCriterionShell.predicate_spec
    (S : IdentityCenteredExceptionalLocalCriterionShell) :
    S.predicate =
      ∀ T : Triplet,
        T ∈ identityCenteredTriplets →
          satisfiesExceptionalLocalPredicateOnIdentityTriplets T →
            ∃ W : IdentityCenteredExceptionalWitness, W.candidate.triplet = T := by
  exact S.predicate_eq

/--
Le prédicat local synthétique global porté par le shell canonique
est bien vérifié : dès qu’un triplet de la famille identité satisfait
le critère local synthétique, on dispose d’un témoin explicite empaqueté.
-/
theorem identityCenteredExceptionalLocalCriterionShell_true :
    identityCenteredExceptionalLocalCriterionShell.predicate := by
  intro T _hmem hcrit
  exact
    isExceptionalCandidateOnIdentityTriplets_hasExplicitWitness
      ((satisfiesExceptionalLocalPredicateOnIdentityTriplets_iff (T := T)).mp hcrit)

/--
Version calculatoire : décidabilité locale purement documentaire
du prédicat empaqueté par le shell canonique.
-/
def identityCenteredExceptionalLocalCriterionShellDecidable :
    Decidable identityCenteredExceptionalLocalCriterionShell.predicate :=
  identityCenteredExceptionalLocalCriterionShell.decidablePredicate

/--
Cas Couret : le shell local sur la famille identité fournit bien
un témoin explicite pour le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionShell_witness :
    ∃ W : IdentityCenteredExceptionalWitness, W.candidate.triplet = couretTriplet := by
  exact
    identityCenteredExceptionalLocalCriterionShell_true
      couretTriplet
      couretTriplet_mem_identityCenteredTriplets
      couretExceptionalLocalPredicateOnIdentityTriplets_true

/--
Cas Couret : le prédicat empaqueté par le shell canonique
sur la famille identité est bien vrai.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionShell_true :
    identityCenteredExceptionalLocalCriterionShell.predicate := by
  exact identityCenteredExceptionalLocalCriterionShell_true

/--
Validation groupée minimale du shell purement local
sur la famille identité :
- le paquet documentaire sous-jacent a bien ses 4 tables de longueur 21 ;
- le prédicat empaqueté est vrai ;
- le cas Couret admet bien un témoin explicite.
-/
theorem exceptionalLocalCriterionShellOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionShell.package.criterionTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionShell.package.witnessTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionShell.package.coreViewTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionShell.package.summaryTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionShell.predicate
      ∧ (∃ W : IdentityCenteredExceptionalWitness, W.candidate.triplet = couretTriplet) := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionShell.package.criterionTable_len,
    identityCenteredExceptionalLocalCriterionShell.package.witnessTable_len,
    identityCenteredExceptionalLocalCriterionShell.package.coreViewTable_len,
    identityCenteredExceptionalLocalCriterionShell.package.summaryTable_len,
    identityCenteredExceptionalLocalCriterionShell_true,
    couretIdentityCenteredExceptionalLocalCriterionShell_witness
  ⟩

end

end CouretUnification.Core