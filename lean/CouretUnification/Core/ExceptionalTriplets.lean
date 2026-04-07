import CouretUnification.Core.Mod30
import Mathlib.Tactic

namespace CouretUnification.Core

/--
Triplet strictement ordonné d'indices actifs.
On travaille en ordre croissant pour éviter les duplications par permutation.
-/
structure Triplet where
  a : Idx
  b : Idx
  c : Idx
  strictlyOrdered : a.1 < b.1 ∧ b.1 < c.1
  deriving DecidableEq

def tripletSupport (T : Triplet) : List Idx := [T.a, T.b, T.c]

def tripletResidues (T : Triplet) : List Nat :=
  [residueVal T.a, residueVal T.b, residueVal T.c]

/--
Constructeur utilitaire : fabrique un triplet (i,j,k) avec i<j<k<8.
-/
def mkTriplet (i j k : Nat) (hij : i < j) (hjk : j < k) (hk : k < 8) : Triplet :=
  { a := ⟨i, lt_trans hij (lt_trans hjk hk)⟩
  , b := ⟨j, lt_trans hjk hk⟩
  , c := ⟨k, hk⟩
  , strictlyOrdered := ⟨hij, hjk⟩
  }

/-
Les 21 triplets contenant l'identité (indice 0),
c'est-à-dire les 21 choix de deux indices parmi {1,2,3,4,5,6,7}.
-/
def identityCenteredTriplets : List Triplet :=
  [ mkTriplet 0 1 2 (by decide) (by decide) (by decide)
  , mkTriplet 0 1 3 (by decide) (by decide) (by decide)
  , mkTriplet 0 1 4 (by decide) (by decide) (by decide)
  , mkTriplet 0 1 5 (by decide) (by decide) (by decide)
  , mkTriplet 0 1 6 (by decide) (by decide) (by decide)
  , mkTriplet 0 1 7 (by decide) (by decide) (by decide)

  , mkTriplet 0 2 3 (by decide) (by decide) (by decide)
  , mkTriplet 0 2 4 (by decide) (by decide) (by decide)
  , mkTriplet 0 2 5 (by decide) (by decide) (by decide)
  , mkTriplet 0 2 6 (by decide) (by decide) (by decide)
  , mkTriplet 0 2 7 (by decide) (by decide) (by decide)

  , mkTriplet 0 3 4 (by decide) (by decide) (by decide)
  , mkTriplet 0 3 5 (by decide) (by decide) (by decide)
  , mkTriplet 0 3 6 (by decide) (by decide) (by decide)
  , mkTriplet 0 3 7 (by decide) (by decide) (by decide)

  , mkTriplet 0 4 5 (by decide) (by decide) (by decide)
  , mkTriplet 0 4 6 (by decide) (by decide) (by decide)
  , mkTriplet 0 4 7 (by decide) (by decide) (by decide)

  , mkTriplet 0 5 6 (by decide) (by decide) (by decide)
  , mkTriplet 0 5 7 (by decide) (by decide) (by decide)

  , mkTriplet 0 6 7 (by decide) (by decide) (by decide)
  ]

lemma identityCenteredTriplets_length :
    identityCenteredTriplets.length = 21 := by
  native_decide

/-- Alias de travail : triplets bruts du noyau fini. -/
def rawTriplets : List Triplet := identityCenteredTriplets

lemma rawTriplets_length : rawTriplets.length = 21 := by
  simpa [rawTriplets] using identityCenteredTriplets_length

/-
À ce stade, on n'encode pas encore la propriété `hasIntegralSpectrum` :
elle doit dépendre d'une vraie couche harmonique finie, pas d'un placeholder.
-/

end CouretUnification.Core