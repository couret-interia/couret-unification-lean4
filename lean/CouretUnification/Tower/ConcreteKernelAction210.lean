import CouretUnification.Tower.ConcreteKernel210
import CouretUnification.Tower.ConcreteCharacters210Lift

open CouretUnification.H3PrimorialTower
open CouretUnification.ConcreteKernel210
open CouretUnification.ConcreteCharacters210Lift
open CouretUnification.ConcreteTransition30To210

namespace CouretUnification
namespace ConcreteKernelAction210

noncomputable section

/-
  Objectif :
  Introduire une action (encore simple) du noyau sur les caractères 210.

  Philosophie :
  - rester conservative (pas de fausse bijection)
  - préparer la génération des lifts
-/

/-- Type du noyau (version sous-type Lean) -/
abbrev Kernel210 := { u : UMod 210 // u ∈ kernelTransition30To210 }

/-- Action (prototype) du noyau sur un caractère.

Pour l'instant :
- on laisse l'action triviale (identité)
- cela permet de brancher toute l'infrastructure sans bloquer
- sera enrichi ensuite
-/
def kernelAction (u : Kernel210) (χ : Character 210) : Character 210 :=
  χ

@[simp]
theorem kernelAction_apply (u : Kernel210) (χ : Character 210) (x : UMod 210) :
    kernelAction u χ x = χ x :=
  rfl

/--
L'action préserve la propriété "être un lift du trivial".
-/
theorem kernelAction_preserves_lift :
    ∀ (u : Kernel210) (χ : Character 210),
      isLiftOfTrivial30 χ →
      isLiftOfTrivial30 (kernelAction u χ) := by
  intro u χ hχ
  simpa [kernelAction] using hχ

/--
L'action fixe le trivial (normal à ce stade).
-/
theorem kernelAction_trivial_fixed (u : Kernel210) :
    kernelAction u ConcreteCharacters210.trivialCharacter210 =
    ConcreteCharacters210.trivialCharacter210 :=
  rfl

/--
Application de l'action à un lift candidat.
-/
def kernelActionOnLift (u : Kernel210) (L : LiftCandidate210) :
    LiftCandidate210 :=
  ⟨kernelAction u L.toCharacter⟩

@[simp]
theorem kernelActionOnLift_apply (u : Kernel210) (L : LiftCandidate210) :
    (kernelActionOnLift u L).toCharacter =
    kernelAction u L.toCharacter :=
  rfl

/--
Les lifts restent valides après action.
-/
theorem kernelAction_preserves_liftCandidates :
    ∀ (u : Kernel210) (L : LiftCandidate210),
      isLiftOfTrivial30 L.toCharacter →
      isLiftOfTrivial30 (kernelActionOnLift u L).toCharacter := by
  intro u L hL
  simpa [kernelActionOnLift] using
    kernelAction_preserves_lift u L.toCharacter hL

/--
Résumé de l'action du noyau.
-/
structure ConcreteKernelActionSummary where
  kernelCardinality : ℕ
  actionDefined : Bool
  actionNonTrivial : Bool
  preservesLiftStructure : Bool
  generatesFullFiber : Bool
deriving Repr

def canonicalConcreteKernelActionSummary :
    ConcreteKernelActionSummary where
  kernelCardinality := kernelTransition30To210Finset.card
  actionDefined := true
  actionNonTrivial := false
  preservesLiftStructure := true
  generatesFullFiber := false

theorem canonicalConcreteKernelActionSummary_doctrine :
    canonicalConcreteKernelActionSummary.kernelCardinality = 6 ∧
    canonicalConcreteKernelActionSummary.actionDefined = true ∧
    canonicalConcreteKernelActionSummary.actionNonTrivial = false ∧
    canonicalConcreteKernelActionSummary.preservesLiftStructure = true ∧
    canonicalConcreteKernelActionSummary.generatesFullFiber = false := by
  simp [
    canonicalConcreteKernelActionSummary,
    ConcreteKernel210.kernelTransition30To210Finset_card
  ]

end
end ConcreteKernelAction210
end CouretUnification
