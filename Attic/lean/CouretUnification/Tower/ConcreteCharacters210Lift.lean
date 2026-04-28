import CouretUnification.Tower.ConcreteCharacters210
import CouretUnification.Tower.ConcreteKernel210

open CouretUnification.H3PrimorialTower

namespace CouretUnification
namespace ConcreteCharacters210Lift

noncomputable section

/-
  Objectif :
  Introduire une couche intermédiaire entre :
  - caractères concrets (actuellement minimal : trivial)
  - structure du noyau (cardinal 6)

  On formalise ici des "candidats de lift" du trivial modulo 30.
-/

/-- Un candidat de relèvement au niveau 210. -/
structure LiftCandidate210 where
  toCharacter : Character 210

/-- Le candidat trivial (lift actuel unique). -/
def trivialLiftCandidate : LiftCandidate210 where
  toCharacter := ConcreteCharacters210.trivialCharacter210

@[simp]
theorem trivialLiftCandidate_apply (u : UMod 210) :
    trivialLiftCandidate.toCharacter u = 1 :=
  rfl

/--
Propriété conservative :
un caractère modulo 210 est actuellement reconnu comme "lift du trivial modulo 30"
s'il coïncide avec le pullback du trivial modulo 30.
-/
def isLiftOfTrivial30 (χ : Character 210) : Prop :=
  χ =
    pullbackChar
      ConcreteCharacters210.transition30To210
      (trivialCharacter 30)

@[simp]
theorem trivialLift_is_valid :
    isLiftOfTrivial30 ConcreteCharacters210.trivialCharacter210 := by
  simpa [isLiftOfTrivial30] using
    ConcreteCharacters210.pullback_trivial_30_to_210.symm

/--
Ensemble actuel des lifts visibles (minimal).
-/
def visibleLiftCandidates210 : Finset LiftCandidate210 :=
  {trivialLiftCandidate}

/--
Cardinal actuel (1).
-/
@[simp]
theorem card_visibleLiftCandidates210 :
    visibleLiftCandidates210.card = 1 := by
  simp [visibleLiftCandidates210]

/--
Projection des candidats vers les caractères.
-/
def liftToCharacter (L : LiftCandidate210) : Character 210 :=
  L.toCharacter

/--
Tous les candidats visibles sont bien des lifts du trivial.
-/
theorem visibleLifts_are_valid :
    ∀ L ∈ visibleLiftCandidates210,
      isLiftOfTrivial30 (liftToCharacter L) := by
  intro L hL
  simp [visibleLiftCandidates210] at hL
  rcases hL with rfl
  exact trivialLift_is_valid

/--
Objectif futur : famille complète de lifts (cardinal attendu 6).
-/
def fullLiftFamilyHasTargetCardinality : Prop :=
  visibleLiftCandidates210.card = 6

/--
Résumé exportable de la couche "lift".
-/
structure ConcreteCharacters210LiftSummary where
  visibleLiftCount : ℕ
  targetLiftCount : ℕ
  allVisibleAreValid : Bool
  fullyConstructed : Bool
  expectedKernelMatch : Bool
deriving Repr

def canonicalConcreteCharacters210LiftSummary :
    ConcreteCharacters210LiftSummary where
  visibleLiftCount := visibleLiftCandidates210.card
  targetLiftCount := 6
  allVisibleAreValid := true
  fullyConstructed := false
  expectedKernelMatch := true

theorem canonicalConcreteCharacters210LiftSummary_doctrine :
    canonicalConcreteCharacters210LiftSummary.visibleLiftCount = 1 ∧
    canonicalConcreteCharacters210LiftSummary.targetLiftCount = 6 ∧
    canonicalConcreteCharacters210LiftSummary.allVisibleAreValid = true ∧
    canonicalConcreteCharacters210LiftSummary.fullyConstructed = false ∧
    canonicalConcreteCharacters210LiftSummary.expectedKernelMatch = true := by
  simp [
    canonicalConcreteCharacters210LiftSummary,
    card_visibleLiftCandidates210
  ]

end
end ConcreteCharacters210Lift
end CouretUnification
