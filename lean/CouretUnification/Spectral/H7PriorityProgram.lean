import CouretUnification.Spectral.H7BridgeProgram

namespace CouretUnification
namespace H7PriorityProgram

open H6NoGo
open H7BridgeProgram

/-- Priority level assigned to a bridge step. -/
inductive PriorityLevel where
  | foundational
  | primary
  | secondary
  | terminal
deriving DecidableEq, Repr

/-- A bridge step together with its doctrinal priority. -/
structure PrioritizedBridgeStep where
  step : BridgeStep
  priority : PriorityLevel

/-- Canonical doctrinal priority assignment for the H7 programme.

The intended order is:
1. microlocal control,
2. character decomposition,
3. prime-resolved lifting,
4. final spectral identification. -/
structure H7PriorityRecord where
  baseProgram : H7ProgramRecord
  microlocal : PrioritizedBridgeStep
  character : PrioritizedBridgeStep
  primeResolved : PrioritizedBridgeStep
  spectralIdentification : PrioritizedBridgeStep

/-- Canonical priority structure exported from H7. -/
def canonicalH7PriorityRecord : H7PriorityRecord :=
  { baseProgram := canonicalH7ProgramRecord
    microlocal := {
      step := canonicalH7ProgramRecord.microlocalStep
      priority := PriorityLevel.foundational
    }
    character := {
      step := canonicalH7ProgramRecord.characterStep
      priority := PriorityLevel.primary
    }
    primeResolved := {
      step := canonicalH7ProgramRecord.primeResolvedStep
      priority := PriorityLevel.secondary
    }
    spectralIdentification := {
      step := canonicalH7ProgramRecord.spectralIdentificationStep
      priority := PriorityLevel.terminal
    } }

/-- The canonical priority order is fixed as doctrine. -/
theorem canonicalH7Priority_doctrine :
    canonicalH7PriorityRecord.microlocal.priority = PriorityLevel.foundational
    ∧ canonicalH7PriorityRecord.character.priority = PriorityLevel.primary
    ∧ canonicalH7PriorityRecord.primeResolved.priority = PriorityLevel.secondary
    ∧ canonicalH7PriorityRecord.spectralIdentification.priority = PriorityLevel.terminal := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The underlying programme remains candidate-level. -/
theorem canonicalH7Priority_inherits_candidate_status :
    canonicalH7PriorityRecord.baseProgram.globalStatus = ProgramStatus.candidate := by
  rfl

/-- Nonempty existence of the prioritized bridge programme. -/
theorem finite_H7Priority_exists : Nonempty H7PriorityRecord := by
  exact ⟨canonicalH7PriorityRecord⟩

/-- Compact summary for publication-facing export. -/
structure BridgePrioritySummary where
  noGoStatus : NoGoStatus
  microlocalPriority : PriorityLevel
  characterPriority : PriorityLevel
  primeResolvedPriority : PriorityLevel
  spectralIdentificationPriority : PriorityLevel
  globalProgramStatus : ProgramStatus

def canonicalBridgePrioritySummary : BridgePrioritySummary :=
  { noGoStatus := canonicalH7PriorityRecord.baseProgram.noGo.status
    microlocalPriority := canonicalH7PriorityRecord.microlocal.priority
    characterPriority := canonicalH7PriorityRecord.character.priority
    primeResolvedPriority := canonicalH7PriorityRecord.primeResolved.priority
    spectralIdentificationPriority := canonicalH7PriorityRecord.spectralIdentification.priority
    globalProgramStatus := canonicalH7PriorityRecord.baseProgram.globalStatus }

/-- Canonical doctrine for the priority summary. -/
theorem canonicalBridgePrioritySummary_doctrine :
    canonicalBridgePrioritySummary.noGoStatus = NoGoStatus.conditional
    ∧ canonicalBridgePrioritySummary.microlocalPriority = PriorityLevel.foundational
    ∧ canonicalBridgePrioritySummary.characterPriority = PriorityLevel.primary
    ∧ canonicalBridgePrioritySummary.primeResolvedPriority = PriorityLevel.secondary
    ∧ canonicalBridgePrioritySummary.spectralIdentificationPriority = PriorityLevel.terminal
    ∧ canonicalBridgePrioritySummary.globalProgramStatus = ProgramStatus.candidate := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace FiniteDoctrine

theorem priority_program_starts_from_conditional_barrier :
    canonicalH7PriorityRecord.baseProgram.noGo.status = NoGoStatus.conditional := by
  rfl

theorem microlocal_is_foundational :
    canonicalH7PriorityRecord.microlocal.priority = PriorityLevel.foundational := by
  rfl

theorem character_is_primary :
    canonicalH7PriorityRecord.character.priority = PriorityLevel.primary := by
  rfl

theorem prime_resolved_is_secondary :
    canonicalH7PriorityRecord.primeResolved.priority = PriorityLevel.secondary := by
  rfl

theorem spectral_identification_is_terminal :
    canonicalH7PriorityRecord.spectralIdentification.priority = PriorityLevel.terminal := by
  rfl

theorem priority_program_summary :
    canonicalBridgePrioritySummary.noGoStatus = NoGoStatus.conditional
    ∧ canonicalBridgePrioritySummary.microlocalPriority = PriorityLevel.foundational
    ∧ canonicalBridgePrioritySummary.characterPriority = PriorityLevel.primary
    ∧ canonicalBridgePrioritySummary.primeResolvedPriority = PriorityLevel.secondary
    ∧ canonicalBridgePrioritySummary.spectralIdentificationPriority = PriorityLevel.terminal
    ∧ canonicalBridgePrioritySummary.globalProgramStatus = ProgramStatus.candidate := by
  exact canonicalBridgePrioritySummary_doctrine

end FiniteDoctrine

end H7PriorityProgram
end CouretUnification
