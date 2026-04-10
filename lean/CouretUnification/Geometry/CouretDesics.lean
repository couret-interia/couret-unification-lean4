import CouretUnification.FunctionalFoundation.DiscreteConnection

namespace CouretUnification.Geometry
open CouretUnification.FunctionalFoundation
open CouretUnification.FunctionalFoundation.Path

/-!
# CouretDesics

Ce fichier compare deux notions de minimisation sur les chemins discrets :

- la version **classique**, qui minimise seulement `edgeEnergy` ;
- la version **Couret**, qui minimise `pathEnergy`, donc
  énergie locale + correction globale.

Convention InterIA :
- on conserve les anciens noms historiques (`Desic`) pour éviter de casser
  les imports existants ;
- on expose en plus des alias plus lisibles (`Geodesic`) pour la suite.
-/

section Defs

variable {α R : Type*} [LinearOrder R] [AddCommMonoid R]

/-- Géodésique discrète classique :
`p` minimise l’énergie locale parmi les chemins de même longueur
et de mêmes extrémités. -/
def IsClassicalDiscreteGeodesic
    (L : DiscreteLagrangian α R) (a b : α) {n : Nat}
    (p : Path α n) : Prop :=
  HasEndpoints a b p ∧
    ∀ q : Path α n, HasEndpoints a b q → edgeEnergy L p ≤ edgeEnergy L q

/-- Version historique du dépôt :
`p` minimise l’énergie totale, c’est-à-dire l’énergie des arêtes
plus la correction globale. -/
def IsCouretDesic
    (L : DiscreteLagrangian α R) (a b : α) {n : Nat}
    (p : Path α n) : Prop :=
  HasEndpoints a b p ∧
    ∀ q : Path α n, HasEndpoints a b q → pathEnergy L p ≤ pathEnergy L q

/-- Alias recommandé pour la suite du développement. -/
abbrev IsCouretGeodesic
    (L : DiscreteLagrangian α R) (a b : α) {n : Nat}
    (p : Path α n) : Prop :=
  IsCouretDesic L a b p

/-- Existence d’un minimiseur Couret pour une longueur fixée. -/
def HasMinimalCouretDesic
    (L : DiscreteLagrangian α R) (a b : α) (n : Nat) : Prop :=
  ∃ p : Path α n, IsCouretDesic L a b p

/-- Alias recommandé pour la suite du développement. -/
abbrev HasMinimalCouretGeodesic
    (L : DiscreteLagrangian α R) (a b : α) (n : Nat) : Prop :=
  HasMinimalCouretDesic L a b n

/-- Si la correction est nulle sur tout chemin, alors la notion
historique de desique Couret se réduit à la notion classique. -/
theorem couretDesic_reduces_to_classical
    (L : DiscreteLagrangian α R)
    (h0 : ZeroCorrection L) {a b : α} {n : Nat} {p : Path α n} :
    IsCouretDesic L a b p ↔ IsClassicalDiscreteGeodesic L a b p := by
  constructor
  · rintro ⟨hend, hmin⟩
    refine ⟨hend, ?_⟩
    intro q hq
    simpa [pathEnergy_eq_edgeEnergy (L := L) h0 (p := p),
      pathEnergy_eq_edgeEnergy (L := L) h0 (p := q)] using hmin q hq
  · rintro ⟨hend, hmin⟩
    refine ⟨hend, ?_⟩
    intro q hq
    simpa [pathEnergy_eq_edgeEnergy (L := L) h0 (p := p),
      pathEnergy_eq_edgeEnergy (L := L) h0 (p := q)] using hmin q hq

/-- Version au nom harmonisé du théorème précédent. -/
theorem couretGeodesic_reduces_to_classical
    (L : DiscreteLagrangian α R)
    (h0 : ZeroCorrection L) {a b : α} {n : Nat} {p : Path α n} :
    IsCouretGeodesic L a b p ↔ IsClassicalDiscreteGeodesic L a b p := by
  simpa [IsCouretGeodesic] using
    (couretDesic_reduces_to_classical (L := L) (h0 := h0) (a := a) (b := b) (n := n) (p := p))

end Defs

end CouretUnification.Geometry