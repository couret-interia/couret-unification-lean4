import CouretUnification.Core.ExceptionalLocalCriterionBooleanPackageOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Prévisualisation documentaire purement locale, sur la famille finie des
21 triplets centrés sur l’identité, extraite de la table booléenne déjà
empaquetée :

- un triplet de la famille ;
- la valeur booléenne documentaire associée au critère local synthétique.

On n’introduit encore :
- aucun `ExceptionalFilter`,
- aucune décision de classification globale,
- aucun filtrage effectif sur les 21 triplets.
-/
structure IdentityCenteredExceptionalLocalCriterionPreviewEntry where
  triplet : Triplet
  value : Bool

/--
Constructeur canonique :
à partir d’une ligne documentaire booléenne déjà construite,
on en extrait la prévisualisation minimale correspondante.
-/
def canonicalIdentityCenteredExceptionalLocalCriterionPreviewEntry
    (E : IdentityCenteredExceptionalLocalCriterionBooleanEntry) :
    IdentityCenteredExceptionalLocalCriterionPreviewEntry where
  triplet := E.triplet
  value := E.value

/--
Table documentaire purement locale de prévisualisation,
extraite de la table booléenne déjà empaquetée.
-/
def identityCenteredExceptionalLocalCriterionPreviewTable :
    List IdentityCenteredExceptionalLocalCriterionPreviewEntry :=
  identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable.map
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewEntry

/-- La table documentaire locale de prévisualisation a bien longueur 21. -/
theorem identityCenteredExceptionalLocalCriterionPreviewTable_length :
    identityCenteredExceptionalLocalCriterionPreviewTable.length = 21 := by
  simpa [identityCenteredExceptionalLocalCriterionPreviewTable]
    using identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable_len

/-- La projection sur les triplets redonne bien la famille finie source. -/
theorem identityCenteredExceptionalLocalCriterionPreviewTable_triplet :
    identityCenteredExceptionalLocalCriterionPreviewTable.map
        (fun E => E.triplet) =
      identityCenteredTriplets := by
  unfold identityCenteredExceptionalLocalCriterionPreviewTable
  rw [List.map_map]
  have hfun :
      ((fun E => E.triplet) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionPreviewEntry) =
        (fun E => E.triplet) := by
    funext E
    rfl
  rw [hfun]
  exact identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable_triplet

/--
En oubliant la structure de prévisualisation, on retrouve exactement
la projection documentaire `(triplet, bool)` de la table booléenne déjà empaquetée.
-/
theorem identityCenteredExceptionalLocalCriterionPreviewTable_forgetsToBooleanPairs :
    identityCenteredExceptionalLocalCriterionPreviewTable.map
        (fun E => (E.triplet, E.value)) =
      identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable.map
        (fun E => (E.triplet, E.value)) := by
  unfold identityCenteredExceptionalLocalCriterionPreviewTable
  rw [List.map_map]
  have hfun :
      ((fun E => (E.triplet, E.value)) ∘
        canonicalIdentityCenteredExceptionalLocalCriterionPreviewEntry) =
        (fun E => (E.triplet, E.value)) := by
    funext E
    rfl
  rw [hfun]

/--
Cas Couret : entrée de prévisualisation canonique extraite de la ligne booléenne
canonique déjà stabilisée.
-/
def couretIdentityCenteredExceptionalLocalCriterionPreviewEntry :
    IdentityCenteredExceptionalLocalCriterionPreviewEntry :=
  canonicalIdentityCenteredExceptionalLocalCriterionPreviewEntry
    couretIdentityCenteredExceptionalLocalCriterionBooleanEntry

/--
Dans le cas Couret, l’entrée de prévisualisation canonique porte bien
sur le triplet distingué.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewEntry_triplet :
    couretIdentityCenteredExceptionalLocalCriterionPreviewEntry.triplet =
      couretTriplet := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionPreviewEntry,
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewEntry]
    using couretIdentityCenteredExceptionalLocalCriterionBooleanPackage_triplet

/--
Dans le cas Couret, la valeur booléenne documentaire associée
vaut bien `true`.
-/
theorem couretIdentityCenteredExceptionalLocalCriterionPreviewEntry_value :
    couretIdentityCenteredExceptionalLocalCriterionPreviewEntry.value = true := by
  simpa [couretIdentityCenteredExceptionalLocalCriterionPreviewEntry,
    canonicalIdentityCenteredExceptionalLocalCriterionPreviewEntry]
    using couretIdentityCenteredExceptionalLocalCriterionBooleanEntry_value_true

/--
Validation groupée minimale du cas Couret au niveau de la prévisualisation
documentaire purement locale sur la famille identité.
-/
theorem exceptionalLocalCriterionPreviewOnIdentityTriplets_valid :
    identityCenteredExceptionalLocalCriterionPreviewTable.length = 21
      ∧ identityCenteredExceptionalLocalCriterionPreviewTable.map
          (fun E => E.triplet) = identityCenteredTriplets
      ∧ identityCenteredExceptionalLocalCriterionPreviewTable.map
          (fun E => (E.triplet, E.value)) =
            identityCenteredExceptionalLocalCriterionBooleanPackage.booleanTable.map
              (fun E => (E.triplet, E.value))
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewEntry.triplet =
          couretTriplet
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewEntry.value = true := by
  exact ⟨
    identityCenteredExceptionalLocalCriterionPreviewTable_length,
    identityCenteredExceptionalLocalCriterionPreviewTable_triplet,
    identityCenteredExceptionalLocalCriterionPreviewTable_forgetsToBooleanPairs,
    couretIdentityCenteredExceptionalLocalCriterionPreviewEntry_triplet,
    couretIdentityCenteredExceptionalLocalCriterionPreviewEntry_value
  ⟩

end

end CouretUnification.Core