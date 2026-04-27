import CouretUnification.Core.FiniteCore
import CouretUnification.FunctionalFoundation.DiscreteConnection
import CouretUnification.Geometry.CouretDesics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic

/-!
# CouretDesicsCayleyG30

Ce fichier instancie un lagrangien discret sur `ZMod 30` en utilisant une
géométrie de type Cayley, adaptée au cadre Couret–Unification.

## Idée générale

On travaille sur le graphe de Cayley induit par les générateurs `cayleyGens`
sur `ZMod 30`. À cette structure de voisinage, on associe :

- une **énergie d’arête** `cayleyEdgeG30`,
- une **correction de chemin** construite à partir d’un poids centré,
- un **lagrangien discret** `G30Lagrangian`,
- puis un énoncé de **stabilité par automorphisme**.

## Philosophie du fichier

Ce module reste volontairement fini, concret et transparent :

- la partie combinatoire (voisinage de Cayley) est explicite ;
- la partie pondérée est donnée par une fonction `w : ZMod 30 → Rat` ;
- l’invariance étudiée est une invariance de la partie centrée du poids.

On reste ici dans la couche **géométrique finie** du projet :
aucune prétention analytique globale, seulement une structure interne propre,
audit-able, et compatible avec la logique modulaire du noyau fini.
-/

open scoped BigOperators

namespace CouretUnification.Geometry
open FunctionalFoundation
open Core.FiniteCore

section CayleyG30

/--
`IsCayleyNeighbor x y` signifie que `y` est obtenu à partir de `x`
par multiplication par l’un des générateurs de Cayley fixés dans le noyau fini.

Autrement dit, `x` et `y` sont adjacents dans le graphe de Cayley considéré.
-/
def IsCayleyNeighbor (x y : ZMod 30) : Prop :=
  ∃ g ∈ cayleyGens, y = x * g

/--
Poids élémentaire d’une arête dans la géométrie `G30`.

Convention choisie :

- coût `0` sur la diagonale (`x = y`),
- coût `1` si `y` est un voisin de Cayley de `x`,
- coût `2` sinon.

Cette fonction joue le rôle d’une "distance discrète simplifiée" :
les pas autorisés par la structure de Cayley sont favorisés,
les autres transitions restent possibles mais plus coûteuses.
-/
noncomputable def cayleyEdgeG30 (x y : ZMod 30) : Rat := by
  classical
  exact if x = y then 0 else if IsCayleyNeighbor x y then 1 else 2

/--
La diagonale a coût nul pour `cayleyEdgeG30`.
-/
@[simp] theorem cayleyEdgeG30_self (x : ZMod 30) :
    cayleyEdgeG30 x x = 0 := by
  classical
  simp [cayleyEdgeG30]

/--
Moyenne du poids `w` sur l’ensemble fini des résidus admissibles.

Cette moyenne sert de référence pour extraire ensuite la composante centrée
du poids, ce qui permet d’isoler la fluctuation autour du niveau moyen.
-/
noncomputable def meanWeightG30 (w : ZMod 30 → Rat) : Rat :=
  admissibleResidues.sum (fun x => w x) / (admissibleResidues.card : Rat)

/--
Version centrée du poids `w` en un point `x`.

Par définition :
`centeredWeightG30 w x = w x - meanWeightG30 w`.

Le centrage est important conceptuellement :
on ne veut pas mesurer un niveau absolu, mais une déviation relative
par rapport au fond moyen du système.
-/
noncomputable def centeredWeightG30 (w : ZMod 30 → Rat) (x : ZMod 30) : Rat :=
  w x - meanWeightG30 w

/--
Correction totale associée à un chemin discret `p`.

On somme la contribution du poids centré sur tous les sommets visités
par le chemin. Cette correction intervient ensuite comme terme additif
dans le lagrangien discret.
-/
noncomputable def correctionG30 (w : ZMod 30 → Rat) {n : Nat}
    (p : Path (ZMod 30) n) : Rat :=
  Finset.univ.sum (fun i : Fin (n + 1) => centeredWeightG30 w (p i))

/--
Lagrangien discret sur `ZMod 30` construit à partir :

- du coût d’arête `cayleyEdgeG30`,
- de la correction de chemin `correctionG30`.

Ce lagrangien encapsule la géométrie combinatoire locale
et la modulation pondérée globale.
-/
noncomputable def G30Lagrangian (w : ZMod 30 → Rat) :
    DiscreteLagrangian (ZMod 30) Rat where
  edge := cayleyEdgeG30
  correction := correctionG30 w

/--
Invariant de poids centré sous un automorphisme `φ`.

On demande ici non pas l’invariance du poids brut `w`,
mais l’invariance de sa version centrée. C’est la bonne notion
dans ce cadre, puisque la correction du lagrangien dépend précisément
de la partie centrée.
-/
def AutomorphismInvariantWeight (w : ZMod 30 → Rat)
    (φ : ZMod 30 ≃ ZMod 30) : Prop :=
  ∀ x : ZMod 30, centeredWeightG30 w (φ x) = centeredWeightG30 w x

/--
La correction discrète est inchangée lorsqu’on applique à un chemin
un automorphisme qui préserve le poids centré.

Lecture conceptuelle :
si `φ` respecte la structure pondérée centrée, alors la "charge totale"
portée par un chemin reste identique après transport du chemin par `φ`.
-/
theorem correctionG30_automorph (w : ZMod 30 → Rat)
    {φ : ZMod 30 ≃ ZMod 30} (hw : AutomorphismInvariantWeight w φ)
    {n : Nat} (p : FunctionalFoundation.Path (ZMod 30) n) :
    correctionG30 w (FunctionalFoundation.Path.map φ p) = correctionG30 w p := by
  classical
  unfold correctionG30
  refine Finset.sum_congr rfl ?_
  intro i hi
  simpa [FunctionalFoundation.Path.map] using hw (p i)

/--
Si un automorphisme `φ` préserve à la fois :

- le coût des arêtes,
- le poids centré,

alors il préserve le lagrangien discret tout entier.
-/
theorem G30_preservesLagrangian (w : ZMod 30 → Rat)
    (φ : ZMod 30 ≃ ZMod 30)
    (hedge : ∀ x y, cayleyEdgeG30 (φ x) (φ y) = cayleyEdgeG30 x y)
    (hw : AutomorphismInvariantWeight w φ) :
    PreservesLagrangian (G30Lagrangian w) φ where
  edge_preserved := hedge
  correction_preserved := fun p => correctionG30_automorph w hw p

/--
Existence d’une Couret-desic minimale entre `a` et `b` en longueur `n`
pour le lagrangien `G30Lagrangian w`.

Cette définition ne prouve rien par elle-même :
elle spécialise simplement la notion générale de minimalité
au cas particulier de la géométrie `G30`.
-/
def G30HasMinimalCouretDesic (w : ZMod 30 → Rat)
    (a b : ZMod 30) (n : Nat) : Prop :=
  HasMinimalCouretDesic (G30Lagrangian w) a b n

end CayleyG30
end CouretUnification.Geometry