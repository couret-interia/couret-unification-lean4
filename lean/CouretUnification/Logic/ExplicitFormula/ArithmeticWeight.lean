/-
  Couret-Unification — v35.9.0
  Logic/ExplicitFormula/ArithmeticWeight.lean

  Objet : POIDS ARITHMÉTIQUE ABSTRAIT.

         Ce module résout le problème doctrinal soulevé par la revue
         externe du 24 avril 2026 :

             Ne PAS axiomatiser vonMangoldt dans Frozen.

         La preuve de finitude du PrimeSide NE DÉPEND PAS des propriétés
         profondes de Λ(n). Elle dépend seulement du fait que le poids
         est évalué contre g, et que g s'annule au-delà de son support.

         Donc Frozen ne connaît qu'un `ArithmeticWeight` abstrait. Active
         instancie ce poids par la vraie fonction de von Mangoldt via
         Mathlib (`Nat.ArithmeticFunction.vonMangoldt`).

  Statut     : Frozen-eligible (0 sorry, 0 axiome local, structure pure)
  Layer      : Logic.ExplicitFormula
  Doctrine   : Frozen = 0 sorry + 0 axiome local non autorisé.
               L'existence de vonMangoldt comme poids valide est
               démontrée dans Active, pas axiomatisée ici.
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0

  Changement v35.9-pre → v35.9.0 :
    NOUVEAU module. Dans v35.9-pre, PrimeSide utilisait une fonction
    `vonMangoldt : ℕ → ℝ` opaque. En v35.9.0, on abstrait : Frozen ne
    connaît plus qu'un `ArithmeticWeight`. L'instanciation concrète
    (`weight = vonMangoldt`) est repoussée à Active.

  Pour Bernard.
-/

import Mathlib.Data.Complex.Basic

namespace CouretUnification.Logic.ExplicitFormula

/- ═══════════════════════════════════════════════════════════════════════════
   POIDS ARITHMÉTIQUE ABSTRAIT
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Un poids arithmétique est une fonction ℕ → ℝ.

    Exemples d'instanciations prévues dans Active :
    - `vonMangoldt` : Λ(p^k) = log p, Λ(n) = 0 sinon.
    - `mu` : fonction de Möbius (pour d'autres sides).
    - `constWeight c` : poids constant (pour les tests).

    Aucune propriété n'est supposée ici. La finitude du PrimeSide sous
    support compact ne dépend que du comportement de `g`, pas de `weight`. -/
structure ArithmeticWeight where
  weight : ℕ → ℝ

/-- Le poids trivial (tous les poids nuls). Utile comme instance de test. -/
def ArithmeticWeight.zero : ArithmeticWeight :=
  { weight := fun _ => 0 }

/-- Le poids constant égal à c. Utile comme instance de test. -/
def ArithmeticWeight.const (c : ℝ) : ArithmeticWeight :=
  { weight := fun _ => c }

/- ═══════════════════════════════════════════════════════════════════════════
   COERCION VERS ℂ
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Le poids évalué en n, comme nombre complexe. -/
noncomputable def ArithmeticWeight.cweight
    (Λ : ArithmeticWeight) (n : ℕ) : ℂ :=
  (Λ.weight n : ℂ)

/- ═══════════════════════════════════════════════════════════════════════════
   NOTE DOCTRINALE
   ═══════════════════════════════════════════════════════════════════════════

   Ce module ne DÉFINIT PAS la fonction de von Mangoldt. Il ne la
   suppose pas existante. Il n'en utilise aucune propriété.

   Dans Active, on écrira typiquement :

       import Mathlib.NumberTheory.ArithmeticFunction
       def vonMangoldtWeight : ArithmeticWeight :=
         { weight := fun n => (Nat.ArithmeticFunction.vonMangoldt n : ℝ) }

   Alors les théorèmes Frozen qui travaillent à `ArithmeticWeight`
   abstrait s'appliquent automatiquement à `vonMangoldtWeight`, sans
   axiome intermédiaire.

   C'est la manière propre de respecter l'invariant Frozen :

       Frozen = 0 sorry + 0 axiome local non autorisé.
-/

end CouretUnification.Logic.ExplicitFormula
