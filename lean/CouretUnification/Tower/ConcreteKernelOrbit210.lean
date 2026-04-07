import Mathlib.Data.Finset.Basic
import CouretUnification.Tower.PrimorialCharacterTower
import CouretUnification.Tower.ConcreteKernel210
import CouretUnification.Tower.ConcreteCharacters210
import CouretUnification.Tower.ConcreteCharacters210Lift

open CouretUnification.H3PrimorialTower
open CouretUnification.ConcreteKernel210
open CouretUnification.ConcreteCharacters210
open CouretUnification.ConcreteCharacters210Lift

namespace CouretUnification
namespace ConcreteKernelOrbit210

noncomputable section

abbrev U210 : Type := UMod 210

/--
Sous-type concret du noyau de la transition `210 → 30`.
-/
abbrev Kernel210 : Type :=
  { u : U210 // u ∈ kernelTransition30To210 }

/--
Action conservative actuelle du noyau sur les caractères modulo 210 :
elle est triviale à ce stade.
-/
def kernelAction (u : Kernel210) (χ : Character 210) : Character 210 :=
  χ

@[simp]
theorem kernelAction_def (u : Kernel210) (χ : Character 210) :
    kernelAction u χ = χ :=
  rfl

/--
Orbites finies visibles sous l'action actuelle du noyau.
Comme l'action est encore triviale, l'orbite visible est un singleton.
-/
def kernelOrbit (χ : Character 210) : Finset (Character 210) :=
  {χ}

@[simp]
theorem mem_kernelOrbit_iff (χ ψ : Character 210) :
    ψ ∈ kernelOrbit χ ↔ ψ = χ := by
  simp [kernelOrbit]

@[simp]
theorem kernelOrbit_eq_singleton (χ : Character 210) :
    kernelOrbit χ = {χ} :=
  rfl

@[simp]
theorem kernelOrbit_card (χ : Character 210) :
    (kernelOrbit χ).card = 1 := by
  simp [kernelOrbit]

/--
Caractère de départ : le lift trivial actuellement visible.
-/
def trivialLiftOrbit : Finset (Character 210) :=
  kernelOrbit trivialLiftCandidate.toCharacter

@[simp]
theorem trivialLiftOrbit_eq :
    trivialLiftOrbit = {trivialLiftCandidate.toCharacter} := by
  rfl

@[simp]
theorem trivialLiftOrbit_card :
    trivialLiftOrbit.card = 1 := by
  simp [trivialLiftOrbit, kernelOrbit]

/--
Cible doctrinale future :
quand l'action concrète par le noyau sera effectivement branchée,
l'orbite attendue devra refléter le cardinal du noyau, soit `6`.
-/
def trivialLiftOrbitHasTargetCardinality : Prop :=
  trivialLiftOrbit.card = 6

/--
Résumé exportable de la couche "orbit".
-/
structure ConcreteKernelOrbitSummary where
  currentOrbitCardinality : ℕ
  targetOrbitCardinality : ℕ
  actionStatus : WorkStatus
  orbitStatus : TowerStepStatus
  kernelCardinalityClosed : Bool
  orbitCardinalityClosed : Bool
deriving Repr

def canonicalConcreteKernelOrbitSummary : ConcreteKernelOrbitSummary where
  currentOrbitCardinality := trivialLiftOrbit.card
  targetOrbitCardinality := 6
  actionStatus := WorkStatus.ready
  orbitStatus := TowerStepStatus.scaffolded
  kernelCardinalityClosed := true
  orbitCardinalityClosed := false

theorem canonicalConcreteKernelOrbitSummary_doctrine :
    canonicalConcreteKernelOrbitSummary.currentOrbitCardinality = 1 ∧
    canonicalConcreteKernelOrbitSummary.targetOrbitCardinality = 6 ∧
    canonicalConcreteKernelOrbitSummary.actionStatus = WorkStatus.ready ∧
    canonicalConcreteKernelOrbitSummary.orbitStatus = TowerStepStatus.scaffolded ∧
    canonicalConcreteKernelOrbitSummary.kernelCardinalityClosed = true ∧
    canonicalConcreteKernelOrbitSummary.orbitCardinalityClosed = false := by
  simp [canonicalConcreteKernelOrbitSummary, trivialLiftOrbit]

/--
Version H7 : le noyau est fermé, l'orbite est définie,
mais son cardinal "transporté" n'est pas encore fermé.
-/
structure H7KernelOrbitWorkRecord where
  bridgeStatus : BridgeStatus
  kernelStatus : WorkStatus
  orbitStatus : WorkStatus
  proofStatus : TowerStepStatus
  targetCardinality : ℕ
  theoremAvailable : Bool
deriving Repr

def canonicalH7KernelOrbitWorkRecord : H7KernelOrbitWorkRecord where
  bridgeStatus := BridgeStatus.candidate
  kernelStatus := WorkStatus.done
  orbitStatus := WorkStatus.ready
  proofStatus := TowerStepStatus.scaffolded
  targetCardinality := 6
  theoremAvailable := false

theorem canonicalH7KernelOrbitWorkRecord_doctrine :
    canonicalH7KernelOrbitWorkRecord.bridgeStatus = BridgeStatus.candidate ∧
    canonicalH7KernelOrbitWorkRecord.kernelStatus = WorkStatus.done ∧
    canonicalH7KernelOrbitWorkRecord.orbitStatus = WorkStatus.ready ∧
    canonicalH7KernelOrbitWorkRecord.proofStatus = TowerStepStatus.scaffolded ∧
    canonicalH7KernelOrbitWorkRecord.targetCardinality = 6 ∧
    canonicalH7KernelOrbitWorkRecord.theoremAvailable = false := by
  simp [canonicalH7KernelOrbitWorkRecord]

end
end ConcreteKernelOrbit210
end CouretUnification
