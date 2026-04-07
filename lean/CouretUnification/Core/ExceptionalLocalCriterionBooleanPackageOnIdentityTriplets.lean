import CouretUnification.Core.ExceptionalLocalCriterionBooleanTableOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Paquet documentaire purement local, sur la famille finie des 21 triplets
centrés sur l’identité, regroupant :

- la table propositionnelle du critère local synthétique ;
- la table décidable associée ;
- la table booléenne documentaire associée.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionBooleanPackage where
  criterionTable : List (Triplet × Prop)
  criterionTable_len : criterionTable.length = 21
  criterionTable_triplet :
    criterionTable.map Prod.fst = identityCenteredTriplets

  decidableTable : List IdentityCenteredExceptionalLocalCriterionDecidableEntry
  decidableTable_len : decidableTable.length = 21
  decidableTable_triplet :
    decidableTable.map (fun E => E.triplet) = identityCenteredTriplets
  decidableTable_forgetsToCriterionTable :
    decidableTable.map (fun E => (E.triplet, E.predicate)) = criterionTable

  booleanTable : List IdentityCenteredExceptionalLocalCriterionBooleanEntry
  booleanTable_len : booleanTable.length = 21
  booleanTable_triplet :
    booleanTable.map (fun E => E.triplet) = identityCenteredTriplets
  booleanTable_forgetsToCriterionTable :
    booleanTable.map (fun E => (E.triplet, E.predicate)) = criterionTable

/--
Paquet canonique purement local :
on regroupe simplement les trois tables déjà construites et leurs
cohérences documentaires minimales.
-/
def identityCenteredExceptionalLocalCriterionBooleanPackage :
    IdentityCenteredExceptionalLocalCriterionBooleanPackage where
  criterionTable := identityCenteredExceptionalLocalCriterionTable
  criterionTable_len := identityCenteredExceptionalLocalCriterionTable_length
  criterionTable_triplet := identityCenteredExceptionalLocalCriterionTable_fst

  decidableTable := identityCenteredExceptionalLocalCriterionDecidableTable
  decidableTable_len := identityCenteredExceptionalLocalCriterionDecidableTable_length
  decidableTable_triplet := identityCenteredExceptionalLocalCriterionDecidableTable_triplet
  decidableTable_forgetsToCriterionTable :=
    identityCenteredExceptionalLocalCriterionDecidableTable_forgetsToCriterionTable

  booleanTable := identityCenteredExceptionalLocalCriterionBooleanTable
  booleanTable_len := identityCenteredExceptionalLocalCriterionBooleanTable_length
  booleanTable_triplet := identityCenteredExceptionalLocalCriterionBooleanTable_triplet
  booleanTable_forgetsToCriterionTable :=
    identityCenteredExceptionalLocalCriterionBooleanTable_forgetsToCriterionTable

/-- La table propositionnelle du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionBooleanPackage_criterionTable_length :
    identityCenteredExceptionalLocalCriterionBooleanPackage.criterionTable.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionBooleanPackage.criterionTable_len

/-- La table décidable du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionBooleanPackage_decidableTable_length :
    identityCenteredExceptionalLocalCriterionBooleanPackage.decidableTable.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionBooleanPackage.decidableTable_len

/-- La table booléenne du paquet canonique a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionBooleanPackage_booleanTable_length :
    identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable.length = 21 := by
  exact identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable_len

/-- Toutes les projections sur les triplets redonnent bien la famille identité. -/
theorem identityCenteredExceptionalLocalCriterionBooleanPackage_triplet_projections :
    identityCenteredExceptionalLocalCriterionBooleanPackage.criterionTable.map Prod.fst =
        identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionBooleanPackage.decidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionBooleanPackage.criterionTable_triplet,
    identityCenteredExceptionalLocalCriterionBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable_triplet
  ⟩

/--
Les deux tables enrichies oublient bien vers la même table documentaire
propositionnelle du critère local synthétique.
-/
theorem identityCenteredExceptionalLocalCriterionBooleanPackage_forgetful_coherence :
    identityCenteredExceptionalLocalCriterionBooleanPackage.decidableTable.map
        (fun E => (E.triplet, E.predicate)) =
          identityCenteredExceptionalLocalCriterionBooleanPackage.criterionTable
      ∧ identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable.map
          (fun E => (E.triplet, E.predicate)) =
            identityCenteredExceptionalLocalCriterionBooleanPackage.criterionTable := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionBooleanPackage.decidableTable_forgetsToCriterionTable,
    identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable_forgetsToCriterionTable
  ⟩

/--
Cas Couret : la ligne booléenne canonique porte bien sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionBooleanPackage_triplet :
    couretIdentityCenteredExceptionalLocalCriterionBooleanEntry.triplet = couretTriplet := by
  rfl

/--
Cas Couret : le critère local synthétique empaqueté dans la ligne décidable
canonique est bien satisfait.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionBooleanPackage_predicate :
    couretIdentityCenteredExceptionalLocalCriterionDecidableEntry.predicate := by
  exact couretIdentityCenteredExceptionalLocalCriterionDecidableEntry_true

/--
Validation groupée minimale du paquet canonique purement local
au niveau propositionnel / décidable / booléen sur la famille identité.
-/
theorem exceptionalLocalCriterionBooleanPackageOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionBooleanPackage.criterionTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionBooleanPackage.decidableTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionBooleanPackage.criterionTable.map Prod.fst =
          identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionBooleanPackage.decidableTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionBooleanPackage.decidableTable.map
          (fun E => (E.triplet, E.predicate)) =
            identityCenteredExceptionalLocalCriterionBooleanPackage.criterionTable
      ∧ identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable.map
          (fun E => (E.triplet, E.predicate)) =
            identityCenteredExceptionalLocalCriterionBooleanPackage.criterionTable
      ∧ couretIdentityCenteredExceptionalLocalCriterionDecidableEntry.predicate
      ∧ couretIdentityCenteredExceptionalLocalCriterionBooleanEntry.triplet = couretTriplet := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionBooleanPackage_criterionTable_length,
    identityCenteredExceptionalLocalCriterionBooleanPackage_decidableTable_length,
    identityCenteredExceptionalLocalCriterionBooleanPackage_booleanTable_length,
    identityCenteredExceptionalLocalCriterionBooleanPackage.criterionTable_triplet,
    identityCenteredExceptionalLocalCriterionBooleanPackage.decidableTable_triplet,
    identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable_triplet,
    identityCenteredExceptionalLocalCriterionBooleanPackage.decidableTable_forgetsToCriterionTable,
    identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable_forgetsToCriterionTable,
    couretIdentityCenteredExceptionalLocalCriterionBooleanPackage_predicate,
    couretIdentityCenteredExceptionalLocalCriterionBooleanPackage_triplet
  ⟩

end

end CouretUnification.Core