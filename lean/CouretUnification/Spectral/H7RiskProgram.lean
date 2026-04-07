import CouretUnification.Spectral.H7DependencyProgram
import Mathlib.Data.Bool.Basic

namespace CouretUnification
namespace H7RiskProgram

open H6NoGo
open H7BridgeProgram
open H7PriorityProgram
open H7MilestoneProgram
open H7DependencyProgram

/-- Risk level attached to a bridge step. -/
inductive RiskLevel where
  | low
  | medium
  | high
  | critical
deriving DecidableEq, Repr

/-- Main obstacle family attached to a bridge step. -/
inductive ObstacleKind where
  | microlocal
  | characterResolution
  | primeResolvedLifting
  | spectralIdentification
deriving DecidableEq, Repr

/-- Risk descriptor for a single bridge step. -/
structure RiskDescriptor where
  node : BridgeNode
  level : RiskLevel
  obstacle : ObstacleKind
  blocking : Bool
deriving Repr

/-- Full risk map for the H7 bridge programme. -/
structure H7RiskRecord where
  dependency : H7DependencyRecord
  microlocalRisk : RiskDescriptor
  characterRisk : RiskDescriptor
  primeResolvedRisk : RiskDescriptor
  spectralIdentificationRisk : RiskDescriptor

/-- Canonical finite risk map extracted from the current programme doctrine. -/
def canonicalH7RiskRecord : H7RiskRecord :=
  { dependency := canonicalH7DependencyRecord
    microlocalRisk := {
      node := BridgeNode.microlocal
      level := RiskLevel.critical
      obstacle := ObstacleKind.microlocal
      blocking := true
    }
    characterRisk := {
      node := BridgeNode.character
      level := RiskLevel.medium
      obstacle := ObstacleKind.characterResolution
      blocking := false
    }
    primeResolvedRisk := {
      node := BridgeNode.primeResolved
      level := RiskLevel.high
      obstacle := ObstacleKind.primeResolvedLifting
      blocking := false
    }
    spectralIdentificationRisk := {
      node := BridgeNode.spectralIdentification
      level := RiskLevel.critical
      obstacle := ObstacleKind.spectralIdentification
      blocking := true
    } }

/-- Compact doctrinal theorem for the canonical risk map. -/
theorem canonicalH7Risk_doctrine :
    canonicalH7RiskRecord.microlocalRisk.level = RiskLevel.critical ∧
    canonicalH7RiskRecord.microlocalRisk.blocking = true ∧
    canonicalH7RiskRecord.characterRisk.level = RiskLevel.medium ∧
    canonicalH7RiskRecord.primeResolvedRisk.level = RiskLevel.high ∧
    canonicalH7RiskRecord.spectralIdentificationRisk.level = RiskLevel.critical ∧
    canonicalH7RiskRecord.spectralIdentificationRisk.blocking = true := by
  simp [canonicalH7RiskRecord]

/-- The risk map is compatible with the milestone doctrine:
microlocal and spectral identification are the blocking points. -/
theorem canonicalH7Risk_preserves_milestones :
    canonicalH7RiskRecord.dependency.milestone.microlocal.milestone = MilestoneStatus.blocked ∧
    canonicalH7RiskRecord.dependency.milestone.character.milestone = MilestoneStatus.structured ∧
    canonicalH7RiskRecord.dependency.milestone.primeResolved.milestone = MilestoneStatus.scaffolded ∧
    canonicalH7RiskRecord.dependency.milestone.spectralIdentification.milestone = MilestoneStatus.blocked := by
  exact canonicalH7Dependency_preserves_milestones

theorem finite_H7Risk_exists : Nonempty H7RiskRecord := by
  exact ⟨canonicalH7RiskRecord⟩

/-- Publication-oriented summary object for the risk doctrine. -/
structure BridgeRiskSummary where
  noGoStatus : NoGoStatus
  globalProgramStatus : ProgramStatus
  globalMilestone : MilestoneStatus
  microlocalRisk : RiskLevel
  microlocalBlocking : Bool
  characterRisk : RiskLevel
  primeResolvedRisk : RiskLevel
  spectralIdentificationRisk : RiskLevel
  spectralIdentificationBlocking : Bool

def canonicalBridgeRiskSummary : BridgeRiskSummary :=
  { noGoStatus := canonicalBridgeDependencySummary.noGoStatus
    globalProgramStatus := canonicalBridgeMilestoneSummary.globalProgramStatus
    globalMilestone := canonicalBridgeMilestoneSummary.globalMilestone
    microlocalRisk := canonicalH7RiskRecord.microlocalRisk.level
    microlocalBlocking := canonicalH7RiskRecord.microlocalRisk.blocking
    characterRisk := canonicalH7RiskRecord.characterRisk.level
    primeResolvedRisk := canonicalH7RiskRecord.primeResolvedRisk.level
    spectralIdentificationRisk := canonicalH7RiskRecord.spectralIdentificationRisk.level
    spectralIdentificationBlocking := canonicalH7RiskRecord.spectralIdentificationRisk.blocking }

theorem canonicalBridgeRiskSummary_doctrine :
    canonicalBridgeRiskSummary.noGoStatus = NoGoStatus.conditional ∧
    canonicalBridgeRiskSummary.globalProgramStatus = ProgramStatus.candidate ∧
    canonicalBridgeRiskSummary.globalMilestone = MilestoneStatus.structured ∧
    canonicalBridgeRiskSummary.microlocalRisk = RiskLevel.critical ∧
    canonicalBridgeRiskSummary.microlocalBlocking = true ∧
    canonicalBridgeRiskSummary.characterRisk = RiskLevel.medium ∧
    canonicalBridgeRiskSummary.primeResolvedRisk = RiskLevel.high ∧
    canonicalBridgeRiskSummary.spectralIdentificationRisk = RiskLevel.critical ∧
    canonicalBridgeRiskSummary.spectralIdentificationBlocking = true := by
  rcases canonicalBridgeDependencySummary_doctrine with
    ⟨hNoGo, _, _, _, _, _, _⟩
  rcases canonicalBridgeMilestoneSummary_doctrine with
    ⟨_, _, _, _, _, _, _, _, _, hGlobalProgram, hGlobalMilestone⟩
  constructor
  · exact hNoGo
  constructor
  · exact hGlobalProgram
  constructor
  · exact hGlobalMilestone
  · simp [canonicalBridgeRiskSummary, canonicalH7RiskRecord]

end H7RiskProgram
end CouretUnification
