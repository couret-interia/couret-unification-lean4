/-
  Couret-Unification — v35.9.1
  Logic/ExplicitFormula/TestPair.lean

  Objet : couple test minimal pour la couche formule explicite.

         À ce stade Frozen n'a besoin que de la fonction du côté log
         et de son support compact. Aucune théorie de Fourier, aucun
         zéro de ζ, aucun vonMangoldt, aucun digamma.

  Statut     : Frozen-eligible (0 sorry, 0 axiome local, structure pure)
  Layer      : Logic.ExplicitFormula
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0

  Changement v35.9.0 → v35.9.1 :
    Extrait de TestFunctions.lean pour devenir le plus petit bloc
    partageable par PrimeSide, TraceObject, ZeroCounting, ArchimedeanSide
    et ExplicitFormulaBridge.

  Pour Bernard.
-/

import Mathlib.Data.Complex.Basic

namespace CouretUnification.Logic.ExplicitFormula

/-- Couple test minimal. Seuls la fonction `g` du côté logarithmique
    et la compacité de son support sont requis dans Frozen. -/
structure TestPair where
  g                : ℝ → ℂ
  compactSupport_g :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, A < |x| → g x = 0

end CouretUnification.Logic.ExplicitFormula
