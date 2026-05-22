/-
# ResGold/Status.lean

Marqueurs épistémiques du programme Couret–Unification et invariant
de compilation `RHClaimed = false`.

Doctrine héritée de v36 : aucun axiome global ne redescend dans le noyau fini.
Tous les énoncés non démontrés sont marqués `sorry` (local, traçable),
jamais `axiom` (global, dangereux).

Discipline anti-trivialité (v38.3 + v38.5) :
* Pas de Prop nues comme champs de structure (anti-Prop-nue, v38.3).
* Pas de True comme énoncé de théorème (anti-True-énoncé, v38.5).

Auteur : Alexandre Couret (programme), squelette prêt et validé par Thomas.
Statut de ce fichier : [D] (pur, aucun sorry).
-/

namespace CouretUnification.ResGold

/-- Statut épistémique d'un énoncé.

* `D` : démontré / calcul fini exact / formalisable
* `M` : mesuré / numérique / expérimental
* `H` : hypothèse structurée / régularisation plausible
* `O` : ouvert / verrou réel
* `E` : règle épistémique / Gate

Cette structure est purement documentaire — elle n'a pas de contenu
mathématique mais elle permet d'inscrire le statut de chaque définition
dans la signature de type.
-/
inductive ResGoldStatus where
  | D : ResGoldStatus
  | M : ResGoldStatus
  | H : ResGoldStatus
  | O : ResGoldStatus
  | E : ResGoldStatus
deriving DecidableEq, Repr

/-- `RHClaimed` est un drapeau booléen fixé à `false` :
ce module ne revendique pas RH.

La convention v38.5 est uniforme dans le dépôt :
les gardes de revendication globales sont des `Bool := false`,
et non des propositions `Prop := False`. -/
def RHClaimed : Bool := false

/-- Invariant de compilation : RH n'est pas revendiquée. -/
theorem rh_not_claimed : RHClaimed = false := rfl

/-- Gate 0 (statut [E]) — règle d'inscription :
aucune symétrie fonctionnelle s ↔ 1 - s ne peut être supposée ;
elle doit provenir d'une dualité inscrite dans l'espace fonctionnel
(Fourier / Mellin / Pontryagin / Poisson adélique).

Cette gate est une règle épistémique et n'a pas de contenu Lean direct ;
elle est documentée ici comme contrainte sur l'architecture. -/
def gate0_principle : ResGoldStatus := ResGoldStatus.E

end CouretUnification.ResGold
