import CouretUnification.Core.ExceptionalLocalCriterionPreviewFinalExportOnIdentityTriplets
import Mathlib.Tactic

namespace CouretUnification.Core

noncomputable section

/--
Filtrage documentaire purement local des couples finaux `(triplet, bool)` :
on ne conserve que les lignes marquées `true`.

On n’introduit encore :
- aucun `ExceptionalFilter` logique lourd ;
- aucune classification globale ;
- aucun raffinement hors de la famille identité.
-/
def exceptionalLocalCriterionFilteredRows : List (Triplet × Bool) :=
  identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows.filter (fun p => p.2)

/--
Filtre exceptionnel sur la famille des 21 triplets centrés sur l’identité :
projection sur les triplets des seules lignes finales marquées `true`.
-/
def exceptionalFilterOnIdentityTriplets : List Triplet :=
  exceptionalLocalCriterionFilteredRows.map Prod.fst

/--
Toute ligne conservée par le filtrage provient bien de la vue d’export finale.
-/
theorem exceptionalLocalCriterionFilteredRows_subrows
    {p : Triplet × Bool}
    (hp : p ∈ exceptionalLocalCriterionFilteredRows) :
    p ∈ identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows := by
  unfold exceptionalLocalCriterionFilteredRows at hp
  exact (List.mem_filter.mp hp).1

/--
Toute ligne conservée par le filtrage est bien marquée `true`.
-/
theorem exceptionalLocalCriterionFilteredRows_true
    {p : Triplet × Bool}
    (hp : p ∈ exceptionalLocalCriterionFilteredRows) :
    p.2 = true := by
  unfold exceptionalLocalCriterionFilteredRows at hp
  simpa using (List.mem_filter.mp hp).2

/--
Caractérisation du filtre exceptionnel :
un triplet appartient au filtre ssi il apparaît dans la vue d’export finale
avec une valeur booléenne égale à `true`.
-/
theorem exceptionalFilterOnIdentityTriplets_mem_iff
    {T : Triplet} :
    T ∈ exceptionalFilterOnIdentityTriplets ↔
      ∃ p ∈ identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows,
        p.1 = T ∧ p.2 = true := by
  constructor
  · intro hT
    unfold exceptionalFilterOnIdentityTriplets at hT
    rcases List.mem_map.mp hT with ⟨p, hp, hp1⟩
    exact ⟨p,
      exceptionalLocalCriterionFilteredRows_subrows hp,
      hp1,
      exceptionalLocalCriterionFilteredRows_true hp⟩
  · intro h
    rcases h with ⟨p, hrow, hp1, hp2⟩
    unfold exceptionalFilterOnIdentityTriplets
    apply List.mem_map.mpr
    refine ⟨p, ?_, hp1⟩
    unfold exceptionalLocalCriterionFilteredRows
    apply List.mem_filter.mpr
    refine ⟨hrow, ?_⟩
    simp [hp2]

/--
Tout triplet retenu par le filtre exceptionnel appartient bien
à la famille finie des triplets centrés sur l’identité.
-/
theorem exceptionalFilterOnIdentityTriplets_mem_family
    {T : Triplet}
    (hT : T ∈ exceptionalFilterOnIdentityTriplets) :
    T ∈ identityCenteredTriplets := by
  rcases (exceptionalFilterOnIdentityTriplets_mem_iff).mp hT with
    ⟨p, hrow, hp1, _⟩
  have hfst : T ∈ identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows.map Prod.fst := by
    rw [← hp1]
    exact List.mem_map.mpr ⟨p, hrow, rfl⟩
  simpa [identityCenteredExceptionalLocalCriterionPreviewFinalExport_triplet] using hfst

/--
Le nombre de lignes conservées par le filtrage est majoré par `21`.
-/
theorem exceptionalLocalCriterionFilteredRows_length_le :
    exceptionalLocalCriterionFilteredRows.length ≤ 21 := by
  unfold exceptionalLocalCriterionFilteredRows
  calc
    (identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows.filter
      (fun p => p.2)).length
        ≤ identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows.length := by
          simpa using
            List.length_filter_le
              (fun p : Triplet × Bool => p.2)
              identityCenteredExceptionalLocalCriterionPreviewFinalExport.rows
    _ = 21 := by
      exact identityCenteredExceptionalLocalCriterionPreviewFinalExport_length

/--
Le filtre exceptionnel sur les triplets a lui aussi longueur majorée par `21`.
-/
theorem exceptionalFilterOnIdentityTriplets_length_le :
    exceptionalFilterOnIdentityTriplets.length ≤ 21 := by
  unfold exceptionalFilterOnIdentityTriplets
  simpa using exceptionalLocalCriterionFilteredRows_length_le

/--
Cas Couret : le couple documentaire canonique final reste bien `(couretTriplet, true)`.
-/
theorem couretExceptionalFilterCanonicalPair :
    couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair =
      (couretTriplet, true) := by
  exact couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair_eq

/--
Validation groupée minimale du filtre exceptionnel purement local
sur la famille identité.
-/
theorem exceptionalFilterOnIdentityTriplets_valid :
    exceptionalLocalCriterionFilteredRows.length ≤ 21
      ∧ exceptionalFilterOnIdentityTriplets.length ≤ 21
      ∧ (∀ T, T ∈ exceptionalFilterOnIdentityTriplets →
            T ∈ identityCenteredTriplets)
      ∧ couretIdentityCenteredExceptionalLocalCriterionPreviewFinalExportPair =
          (couretTriplet, true) := by
  refine ⟨
    exceptionalLocalCriterionFilteredRows_length_le,
    exceptionalFilterOnIdentityTriplets_length_le,
    ?_,
    couretExceptionalFilterCanonicalPair
  ⟩
  intro T hT
  exact exceptionalFilterOnIdentityTriplets_mem_family hT

end

end CouretUnification.Core