import CouretUnification.FunctionalFoundation.DiscretePaths
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace CouretUnification.FunctionalFoundation
open Path

/-!
# DiscreteConnection

Ce fichier introduit une version minimale d’un lagrangien discret sur les chemins finis.

Philosophie InterIA :
- on sépare l’énergie locale d’arête (`edge`) ;
- de la correction globale de chemin (`correction`) ;
- puis on isole les hypothèses de symétrie sous équivalence de sommets.

Le but est de garder un noyau :
1. court,
2. lisible,
3. facilement réutilisable dans les couches ultérieures.
-/

/-- Lagrangien discret sur un type de sommets `α` à valeurs dans `R`.

- `edge x y` mesure la contribution locale du saut `x → y`.
- `correction p` permet d’ajouter un terme global dépendant de tout le chemin.
-/
structure DiscreteLagrangian (α : Type*) (R : Type*) where
  edge : α → α → R
  correction : {n : Nat} → Path α n → R

section Energy

variable {α R : Type*} [AddCommMonoid R]

/-- Énergie locale d’un chemin : somme des contributions sur chaque arête successive. -/
def edgeEnergy (L : DiscreteLagrangian α R) {n : Nat} (p : Path α n) : R :=
  ∑ t : Fin n, L.edge (p t.castSucc) (p t.succ)

/-- Énergie totale : énergie des arêtes plus correction globale. -/
def pathEnergy (L : DiscreteLagrangian α R) {n : Nat} (p : Path α n) : R :=
  edgeEnergy L p + L.correction p

/-- La correction est nulle sur tout chemin. -/
def ZeroCorrection (L : DiscreteLagrangian α R) : Prop :=
  ∀ {n : Nat} (p : Path α n), L.correction p = 0

/-- Si la correction est identiquement nulle, l’énergie totale coïncide avec l’énergie d’arête. -/
@[simp] theorem pathEnergy_eq_edgeEnergy
    (L : DiscreteLagrangian α R)
    (h0 : ZeroCorrection L) {n : Nat} (p : Path α n) :
    pathEnergy L p = edgeEnergy L p := by
  unfold pathEnergy
  rw [h0 p, add_zero]

end Energy

/-- Invariance d’un lagrangien discret par une équivalence `φ : α ≃ α`.

Deux niveaux sont demandés :
- invariance locale des arêtes ;
- invariance globale du terme correctif.
-/
structure PreservesLagrangian {α R : Type*} [AddCommMonoid R]
    (L : DiscreteLagrangian α R) (φ : α ≃ α) : Prop where
  edge_preserved : ∀ x y, L.edge (φ x) (φ y) = L.edge x y
  correction_preserved : ∀ {n : Nat} (p : Path α n),
    L.correction (Path.map φ p) = L.correction p

section MapEnergy

variable {α R : Type*} [AddCommMonoid R]
variable {L : DiscreteLagrangian α R} {φ : α ≃ α}

/-- L’énergie locale est inchangée sous une symétrie qui préserve le lagrangien. -/
theorem edgeEnergy_map
    (hφ : PreservesLagrangian L φ) {n : Nat} (p : Path α n) :
    edgeEnergy L (Path.map φ p) = edgeEnergy L p := by
  unfold edgeEnergy
  refine Finset.sum_congr rfl ?_
  intro t ht
  change L.edge (φ (p t.castSucc)) (φ (p t.succ)) =
      L.edge (p t.castSucc) (p t.succ)
  simpa using hφ.edge_preserved (p t.castSucc) (p t.succ)

/-- L’énergie totale est inchangée sous une symétrie qui préserve le lagrangien. -/
theorem pathEnergy_map
    (hφ : PreservesLagrangian L φ) {n : Nat} (p : Path α n) :
    pathEnergy L (Path.map φ p) = pathEnergy L p := by
  unfold pathEnergy
  rw [edgeEnergy_map hφ, hφ.correction_preserved]

end MapEnergy

end CouretUnification.FunctionalFoundation