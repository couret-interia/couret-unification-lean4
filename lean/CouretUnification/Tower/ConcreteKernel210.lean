import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import CouretUnification.Tower.PrimorialCharacterTower
import CouretUnification.Tower.ConcreteUnits30
import CouretUnification.Tower.ConcreteTransition30To210

open CouretUnification.H3PrimorialTower
open CouretUnification.ConcreteTransition30To210

namespace CouretUnification
namespace ConcreteKernel210

noncomputable section

abbrev U30 : Type := UMod 30
abbrev U210 : Type := UMod 210

set_option linter.unnecessarySimpa false

/--
Noyau concret de la transition `210 → 30` :
les unités modulo 210 qui se réduisent à `1` modulo 30.
-/
def kernelTransition30To210 : Subgroup U210 where
  carrier := { u : U210 | transition30To210 u = (1 : U30) }
  one_mem' := by
    simpa using transition30To210.map_one
  mul_mem' := by
    intro a b ha hb
    calc
      transition30To210 (a * b)
          = transition30To210 a * transition30To210 b := by
              simpa using transition30To210.map_mul a b
      _ = (1 : U30) * 1 := by rw [ha, hb]
      _ = (1 : U30) := by simp
  inv_mem' := by
    intro a ha
    have h :
        transition30To210 a * transition30To210 a⁻¹ = (1 : U30) := by
      calc
        transition30To210 a * transition30To210 a⁻¹
            = transition30To210 (a * a⁻¹) := by
                rw [← transition30To210.map_mul]
        _ = transition30To210 1 := by simp
        _ = (1 : U30) := by simpa using transition30To210.map_one
    rw [ha] at h
    simpa using h

@[simp]
theorem mem_kernelTransition30To210_iff (u : U210) :
    u ∈ kernelTransition30To210 ↔ transition30To210 u = (1 : U30) :=
  Iff.rfl

@[simp]
theorem one_mem_kernelTransition30To210 :
    (1 : U210) ∈ kernelTransition30To210 := by
  simpa using kernelTransition30To210.one_mem

set_option linter.unnecessarySimpa true

@[simp]
theorem mul_mem_kernelTransition30To210 {a b : U210}
    (ha : a ∈ kernelTransition30To210)
    (hb : b ∈ kernelTransition30To210) :
    a * b ∈ kernelTransition30To210 :=
  kernelTransition30To210.mul_mem ha hb

@[simp]
theorem inv_mem_kernelTransition30To210 {a : U210}
    (ha : a ∈ kernelTransition30To210) :
    a⁻¹ ∈ kernelTransition30To210 :=
  kernelTransition30To210.inv_mem ha

/--
Version finie explicite du noyau, pour les futurs calculs de cardinal.
-/
def kernelTransition30To210Finset : Finset U210 :=
  Finset.univ.filter (fun u : U210 => transition30To210 u = (1 : U30))

@[simp]
theorem mem_kernelTransition30To210Finset_iff (u : U210) :
    u ∈ kernelTransition30To210Finset ↔ u ∈ kernelTransition30To210 := by
  simp [kernelTransition30To210Finset, kernelTransition30To210]

/--
Cible mathématique attendue pour cette couche :
le noyau devrait avoir cardinal `6`.
À ce stade, on l’enregistre seulement comme objectif.
-/
def kernelTransition30To210HasTargetCardinality : Prop :=
  kernelTransition30To210Finset.card = 6

/--
Résumé concret exportable de la couche `kernel210`.
-/
structure ConcreteKernel210Summary where
  bridgeStatus : BridgeStatus
  transitionDefined : Bool
  kernelDefined : Bool
  targetCardinality : ℕ
  actualCardinality : ℕ
  proofStatus : TowerStepStatus
  characterWorkStatus : WorkStatus
deriving Repr

def canonicalConcreteKernel210Summary : ConcreteKernel210Summary where
  bridgeStatus := BridgeStatus.candidate
  transitionDefined := true
  kernelDefined := true
  targetCardinality := 6
  actualCardinality := kernelTransition30To210Finset.card
  proofStatus := TowerStepStatus.scaffolded
  characterWorkStatus := WorkStatus.ready

theorem canonicalConcreteKernel210Summary_doctrine :
    canonicalConcreteKernel210Summary.bridgeStatus = BridgeStatus.candidate ∧
    canonicalConcreteKernel210Summary.transitionDefined = true ∧
    canonicalConcreteKernel210Summary.kernelDefined = true ∧
    canonicalConcreteKernel210Summary.targetCardinality = 6 ∧
    canonicalConcreteKernel210Summary.proofStatus = TowerStepStatus.scaffolded ∧
    canonicalConcreteKernel210Summary.characterWorkStatus = WorkStatus.ready := by
  simp [canonicalConcreteKernel210Summary]

/--
Version H7 : le noyau est défini, mais le cardinal exact reste à fermer.
-/
structure H7KernelWorkRecord where
  bridgeStatus : BridgeStatus
  kernelStepStatus : WorkStatus
  cardinalityProofStatus : TowerStepStatus
  targetCardinality : ℕ
  theoremAvailable : Bool
deriving Repr

def canonicalH7KernelWorkRecord : H7KernelWorkRecord where
  bridgeStatus := BridgeStatus.candidate
  kernelStepStatus := WorkStatus.done
  cardinalityProofStatus := TowerStepStatus.scaffolded
  targetCardinality := 6
  theoremAvailable := false

theorem canonicalH7KernelWorkRecord_doctrine :
    canonicalH7KernelWorkRecord.bridgeStatus = BridgeStatus.candidate ∧
    canonicalH7KernelWorkRecord.kernelStepStatus = WorkStatus.done ∧
    canonicalH7KernelWorkRecord.cardinalityProofStatus = TowerStepStatus.scaffolded ∧
    canonicalH7KernelWorkRecord.targetCardinality = 6 ∧
    canonicalH7KernelWorkRecord.theoremAvailable = false := by
  simp [canonicalH7KernelWorkRecord]

set_option maxRecDepth 4096 in
theorem kernelTransition30To210Finset_card :
    kernelTransition30To210Finset.card = 6 := by
  native_decide

theorem kernelTransition30To210HasTargetCardinality_true :
    kernelTransition30To210HasTargetCardinality := by
  simpa [kernelTransition30To210HasTargetCardinality] using
    kernelTransition30To210Finset_card

def canonicalH7KernelWorkRecord_closed : H7KernelWorkRecord where
  bridgeStatus := BridgeStatus.candidate
  kernelStepStatus := WorkStatus.done
  cardinalityProofStatus := TowerStepStatus.verified
  targetCardinality := 6
  theoremAvailable := true

theorem canonicalH7KernelWorkRecord_closed_doctrine :
    canonicalH7KernelWorkRecord_closed.bridgeStatus = BridgeStatus.candidate ∧
    canonicalH7KernelWorkRecord_closed.kernelStepStatus = WorkStatus.done ∧
    canonicalH7KernelWorkRecord_closed.cardinalityProofStatus = TowerStepStatus.verified ∧
    canonicalH7KernelWorkRecord_closed.targetCardinality = 6 ∧
    canonicalH7KernelWorkRecord_closed.theoremAvailable = true := by
  simp [canonicalH7KernelWorkRecord_closed]

end
end ConcreteKernel210
end CouretUnification
