/-
# ResGold/Status.lean

Marqueurs épistémiques du programme Couret–Unification et invariant
de compilation `RHClaimed = False`.

Doctrine héritée de v36 : aucun axiome global ne redescend dans le noyau fini.
Tous les énoncés non démontrés sont marqués `sorry` (local, traçable),
jamais `axiom` (global, dangereux).

Discipline anti-trivialité (v38.3 + v38.5) :
* Pas de Prop nues comme champs de structure (anti-Prop-nue, v38.3).
* Pas de True comme énoncé de théorème (anti-True-énoncé, v38.5).

Auteur : Alexandre Couret (programme), squelette préparé pour validation Thomas.
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
inductive Status where
  | D : Status
  | M : Status
  | H : Status
  | O : Status
  | E : Status
deriving DecidableEq, Repr

/-- `RHClaimed` est défini comme `False` : ce module n'affirme pas RH.
Toute tentative de dériver RH depuis ce module nécessite de prouver `False`,
ce qui est interdit sans `sorry` ou `axiom` explicite. -/
def RHClaimed : Prop := False

/-- Invariant de compilation : RH n'est pas revendiquée. -/
theorem rh_not_claimed : ¬ RHClaimed := id

/-- Gate 0 (statut [E]) — règle d'inscription :
aucune symétrie fonctionnelle s ↔ 1 - s ne peut être supposée ;
elle doit provenir d'une dualité inscrite dans l'espace fonctionnel
(Fourier / Mellin / Pontryagin / Poisson adélique).

Cette gate est une règle épistémique et n'a pas de contenu Lean direct ;
elle est documentée ici comme contrainte sur l'architecture. -/
def gate0_principle : Status := Status.E

end CouretUnification.ResGold
