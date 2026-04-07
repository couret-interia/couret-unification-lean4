import Mathlib.Data.Finset.Basic
import CouretUnification.Tower.PrimorialCharacterTower
import CouretUnification.Tower.ConcreteKernel210
import CouretUnification.Tower.ConcreteCharacters210
import CouretUnification.Tower.ConcreteCharacters210Lift
import CouretUnification.Tower.ConcreteKernelOrbit210

open CouretUnification.H3PrimorialTower
open CouretUnification.ConcreteKernel210
open CouretUnification.ConcreteCharacters210
open CouretUnification.ConcreteCharacters210Lift
open CouretUnification.ConcreteKernelOrbit210

namespace CouretUnification
namespace ConcreteKernelLiftAction210

noncomputable section
open Classical

abbrev U210 : Type := UMod 210
abbrev Kernel210 : Type := { u : U210 // u ∈ kernelTransition30To210 }

/--
Action conservative actuelle du noyau sur les lifts.
À ce stade, elle laisse chaque lift inchangé.
-/
def kernelLiftAction (_u : Kernel210) (L : LiftCandidate210) : LiftCandidate210 :=
  L

@[simp]
theorem kernelLiftAction_def (u : Kernel210) (L : LiftCandidate210) :
    kernelLiftAction u L = L :=
  rfl

/--
Compatibilité avec l’action triviale déjà définie sur les caractères.
-/
@[simp]
theorem kernelLiftAction_toCharacter (u : Kernel210) (L : LiftCandidate210) :
    liftToCharacter (kernelLiftAction u L) =
      kernelAction u (liftToCharacter L) := by
  rfl

/--
Orbite d’un lift sous l’action actuelle du noyau.
Comme l’action est encore triviale, on obtient un singleton.
-/
def kernelLiftOrbit (L : LiftCandidate210) : Finset LiftCandidate210 :=
  ({L} : Finset LiftCandidate210)

@[simp]
theorem mem_kernelLiftOrbit_iff (L M : LiftCandidate210) :
    M ∈ kernelLiftOrbit L ↔ M = L := by
  simp [kernelLiftOrbit]

@[simp]
theorem kernelLiftOrbit_eq_singleton (L : LiftCandidate210) :
    kernelLiftOrbit L = ({L} : Finset LiftCandidate210) :=
  rfl

@[simp]
theorem kernelLiftOrbit_card (L : LiftCandidate210) :
    (kernelLiftOrbit L).card = 1 := by
  simp [kernelLiftOrbit]

/--
Projection de l’orbite d’un lift vers l’orbite du caractère sous-jacent.
Au stade actuel, les deux sont des singletons.
-/
theorem kernelLiftOrbit_character_projection (L : LiftCandidate210) :
    (kernelLiftOrbit L).image liftToCharacter =
      kernelOrbit (liftToCharacter L) := by
  ext χ
  simp [kernelLiftOrbit, kernelOrbit]

/-- Orbite du lift trivial actuellement disponible. -/
def trivialLiftVisibleOrbit : Finset LiftCandidate210 :=
  kernelLiftOrbit trivialLiftCandidate

@[simp]
theorem trivialLiftVisibleOrbit_eq :
    trivialLiftVisibleOrbit = ({trivialLiftCandidate} : Finset LiftCandidate210) :=
  rfl

@[simp]
theorem trivialLiftVisibleOrbit_card :
    trivialLiftVisibleOrbit.card = 1 := by
  simp [trivialLiftVisibleOrbit, kernelLiftOrbit]

/--
Le lift trivial appartient bien à la liste visible actuelle.
-/
theorem trivialLiftCandidate_mem_visible :
    trivialLiftCandidate ∈ visibleLiftCandidates210 := by
  simp [visibleLiftCandidates210]

/--
Toute l’orbite actuelle du lift trivial reste visible.
-/
theorem trivialLiftVisibleOrbit_subset_visible :
    ∀ {L : LiftCandidate210}, L ∈ trivialLiftVisibleOrbit → L ∈ visibleLiftCandidates210 := by
  intro L hL
  have hEq : L = trivialLiftCandidate := by
    simpa [trivialLiftVisibleOrbit, kernelLiftOrbit] using hL
  rw [hEq]
  exact trivialLiftCandidate_mem_visible

/--
Projection de l’orbite triviale vers l’orbite du caractère trivial lifté.
-/
theorem trivialLiftVisibleOrbit_projects_to_trivialLiftOrbit :
    trivialLiftVisibleOrbit.image liftToCharacter =
      kernelOrbit (liftToCharacter trivialLiftCandidate) := by
  simp [trivialLiftVisibleOrbit]

/--
Cible doctrinale future :
une fois l’action concrète non triviale branchée, l’orbite visible
devra refléter la structure du noyau, avec cardinal attendu `6`.
-/
def trivialLiftVisibleOrbitHasTargetCardinality : Prop :=
  trivialLiftVisibleOrbit.card = 6

/--
Résumé exportable de la couche "kernel action on lifts".
-/
structure ConcreteKernelLiftActionSummary where
  currentOrbitCardinality : ℕ
  targetOrbitCardinality : ℕ
  actionStatus : WorkStatus
  projectionCompatible : Bool
  orbitStatus : TowerStepStatus
  theoremAvailable : Bool
deriving Repr

def canonicalConcreteKernelLiftActionSummary : ConcreteKernelLiftActionSummary where
  currentOrbitCardinality := trivialLiftVisibleOrbit.card
  targetOrbitCardinality := 6
  actionStatus := WorkStatus.ready
  projectionCompatible := true
  orbitStatus := TowerStepStatus.scaffolded
  theoremAvailable := false

theorem canonicalConcreteKernelLiftActionSummary_doctrine :
    canonicalConcreteKernelLiftActionSummary.currentOrbitCardinality = 1 ∧
    canonicalConcreteKernelLiftActionSummary.targetOrbitCardinality = 6 ∧
    canonicalConcreteKernelLiftActionSummary.actionStatus = WorkStatus.ready ∧
    canonicalConcreteKernelLiftActionSummary.projectionCompatible = true ∧
    canonicalConcreteKernelLiftActionSummary.orbitStatus = TowerStepStatus.scaffolded ∧
    canonicalConcreteKernelLiftActionSummary.theoremAvailable = false := by
  simp [canonicalConcreteKernelLiftActionSummary, trivialLiftVisibleOrbit, kernelLiftOrbit]

/--
Version H7 : l’action sur les lifts est installée comme interface,
la compatibilité de projection est fermée, mais le cardinal d’orbite cible
n’est pas encore prouvé.
-/
structure H7KernelLiftActionWorkRecord where
  bridgeStatus : BridgeStatus
  kernelStatus : WorkStatus
  liftActionStatus : WorkStatus
  projectionStatus : WorkStatus
  proofStatus : TowerStepStatus
  targetCardinality : ℕ
  theoremAvailable : Bool
deriving Repr

def canonicalH7KernelLiftActionWorkRecord : H7KernelLiftActionWorkRecord where
  bridgeStatus := BridgeStatus.candidate
  kernelStatus := WorkStatus.done
  liftActionStatus := WorkStatus.ready
  projectionStatus := WorkStatus.done
  proofStatus := TowerStepStatus.scaffolded
  targetCardinality := 6
  theoremAvailable := false

theorem canonicalH7KernelLiftActionWorkRecord_doctrine :
    canonicalH7KernelLiftActionWorkRecord.bridgeStatus = BridgeStatus.candidate ∧
    canonicalH7KernelLiftActionWorkRecord.kernelStatus = WorkStatus.done ∧
    canonicalH7KernelLiftActionWorkRecord.liftActionStatus = WorkStatus.ready ∧
    canonicalH7KernelLiftActionWorkRecord.projectionStatus = WorkStatus.done ∧
    canonicalH7KernelLiftActionWorkRecord.proofStatus = TowerStepStatus.scaffolded ∧
    canonicalH7KernelLiftActionWorkRecord.targetCardinality = 6 ∧
    canonicalH7KernelLiftActionWorkRecord.theoremAvailable = false := by
  simp [canonicalH7KernelLiftActionWorkRecord]

end
end ConcreteKernelLiftAction210
end CouretUnification
