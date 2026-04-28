import CouretUnification.Geometry.CouretDesicsCayleyG30
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

/-!
# Existence de Couret-désiques minimales sur `G30`

Ce module établit un fait fondamental de la géométrie finie sur `ZMod 30` :
pour toute longueur strictement positive et pour toutes extrémités prescrites,
il existe un chemin minimisant l’énergie associée au lagrangien `G30Lagrangian`.

L’idée est volontairement simple et robuste :

- on considère l’ensemble fini des chemins joignant deux extrémités fixées ;
- on montre que cet ensemble est non vide grâce à un chemin trivial explicite ;
- on applique ensuite un principe de minimisation sur ensemble fini.

Lecture InterIA :
ce fichier incarne un principe de compacité finie dans le cadre Couret–Unification :
la minimisation n’est pas obtenue ici par analyse continue, mais par finitude
combinatoire explicite.
-/

namespace CouretUnification.Geometry
open FunctionalFoundation
open FunctionalFoundation.Path

section ExistenceG30

/--
`trivialPathG30 a b hn` est le chemin le plus simple de longueur `n`
entre `a` et `b` dans la géométrie finie `ZMod 30` :

- il reste égal à `a` sur tous les indices intermédiaires ;
- il vaut `b` exactement au dernier indice.

L’hypothèse `hn : 0 < n` garantit que la longueur est strictement positive,
donc que le chemin possède bien une position finale distincte de la position
initiale.

Note InterIA :
ce chemin joue le rôle de témoin canonique de non-vacuité pour l’ensemble
des chemins admissibles à extrémités fixées.
-/
def trivialPathG30 (a b : ZMod 30) {n : Nat} (_ : 0 < n) :
    Path (ZMod 30) n :=
  fun i => if i.1 = n then b else a

/--
Le chemin trivial possède bien les extrémités prescrites.

Autrement dit :
- son départ est `a` ;
- son arrivée est `b`.

La preuve consiste à dérouler directement les définitions de `Path.start`,
`Path.finish` et `trivialPathG30`.
-/
lemma trivialPathG30_endpoints (a b : ZMod 30) {n : Nat} (hn : 0 < n) :
    HasEndpoints a b (trivialPathG30 a b hn) := by
  constructor
  · simp [Path.start, trivialPathG30, Nat.ne_of_lt hn]
  · simp [Path.finish, trivialPathG30]

/--
Existence d’une Couret-désique sur `G30` à extrémités prescrites.

Pour toute fonction de poids `w : ZMod 30 → Rat`, pour tous points
`a b : ZMod 30`, et pour toute longueur positive `n`, il existe un chemin `p`
de longueur `n` tel que :

- `p` part de `a` ;
- `p` arrive en `b` ;
- `p` minimise l’énergie de chemin associée à `G30Lagrangian w`
  parmi tous les chemins ayant les mêmes extrémités.

Stratégie de preuve :
1. Construire l’ensemble fini des chemins de longueur `n` allant de `a` à `b`.
2. Montrer que cet ensemble est non vide grâce à `trivialPathG30`.
3. Appliquer `Finset.exists_min_image`.
4. Réinterpréter le minimiseur obtenu comme une Couret-désique.

Note InterIA :
on exploite ici un principe fondamental de géométrie finie :
**finitude + non-vacuité ⇒ existence d’un minimiseur**.
-/
theorem exists_couretDesicG30 (w : ZMod 30 → Rat)
    (a b : ZMod 30) {n : Nat} (hn : 0 < n) :
    ∃ p : Path (ZMod 30) n,
      IsCouretDesic (G30Lagrangian w) a b p := by
  classical

  /- Ensemble fini des chemins admissibles joignant `a` à `b`. -/
  let admissiblePaths : Finset (Path (ZMod 30) n) :=
    Finset.univ.filter (fun p => HasEndpoints a b p)

  /-
  Cet ensemble est non vide : il contient au moins le chemin trivial,
  construit explicitement ci-dessus.
  -/
  have h_nonempty : admissiblePaths.Nonempty := by
    refine ⟨trivialPathG30 a b hn, ?_⟩
    simpa [admissiblePaths] using
      (Finset.mem_filter.mpr
        ⟨Finset.mem_univ (trivialPathG30 a b hn),
          trivialPathG30_endpoints a b hn⟩)

  /-
  On choisit ensuite un élément `pmin` d’énergie minimale dans cet ensemble fini.
  La propriété `hle` exprime que `pmin` minimise l’énergie sur tout
  l’ensemble `admissiblePaths`.
  -/
  obtain ⟨pmin, hpmin_mem, hle⟩ :=
    Finset.exists_min_image admissiblePaths (pathEnergy (G30Lagrangian w)) h_nonempty

  refine ⟨pmin, ?_, ?_⟩

  · /-
    Première composante : le minimiseur `pmin` possède bien les extrémités
    requises `a` et `b`.
    -/
    have hpmin_mem' :
        pmin ∈ Finset.univ.filter (fun p : Path (ZMod 30) n => HasEndpoints a b p) := by
      simpa [admissiblePaths] using hpmin_mem
    exact (Finset.mem_filter.mp hpmin_mem').2

  · /-
    Seconde composante : tout chemin concurrent `q` ayant les mêmes extrémités
    a une énergie supérieure ou égale à celle de `pmin`.
    -/
    intro q hq
    have hq_mem : q ∈ admissiblePaths := by
      simpa [admissiblePaths] using
        (Finset.mem_filter.mpr
          ⟨Finset.mem_univ q, hq⟩)
    exact hle q hq_mem

/--
Version empaquetée du résultat d’existence :
la géométrie `G30` admet une Couret-désique minimale entre deux extrémités
fixées, pour toute longueur strictement positive.
-/
theorem hasMinimalG30 (w : ZMod 30 → Rat)
    (a b : ZMod 30) {n : Nat} (hn : 0 < n) :
    G30HasMinimalCouretDesic w a b n :=
  exists_couretDesicG30 w a b hn

end ExistenceG30
end CouretUnification.Geometry
