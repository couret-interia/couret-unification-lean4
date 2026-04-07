import CouretUnification.Spectral.H7TimelineProgram

namespace CouretUnification
namespace H7WorkPackageProgram

open H6NoGo
open H7BridgeProgram
open H7PriorityProgram
open H7MilestoneProgram
open H7RiskProgram
open H7TimelineProgram
open H7DependencyProgram

/-- Operational status of a work package. -/
inductive WorkPackageStatus where
  | ready
  | blocked
  | deferred
  | completed
deriving DecidableEq, Repr

/-- A concrete work package attached to one bridge node. -/
structure WorkPackage where
  node : BridgeNode
  priority : PriorityLevel
  milestone : MilestoneStatus
  risk : RiskLevel
  phase : TimelinePhase
  status : WorkPackageStatus
  deliverable : String

/-- H7.6 layer: operational work-package packaging of the bridge programme. -/
structure H7WorkPackageRecord where
  timeline : H7TimelineRecord
  microlocal : WorkPackage
  character : WorkPackage
  primeResolved : WorkPackage
  spectralIdentification : WorkPackage
  globalStatus : WorkPackageStatus

/-- Canonical work-package layer extracted from the timeline programme. -/
def canonicalH7WorkPackageRecord : H7WorkPackageRecord :=
  { timeline := canonicalH7TimelineRecord
    microlocal :=
      { node := BridgeNode.microlocal
        priority := PriorityLevel.foundational
        milestone := MilestoneStatus.blocked
        risk := RiskLevel.critical
        phase := TimelinePhase.blocked
        status := WorkPackageStatus.blocked
        deliverable := "Microlocal control package" }
    character :=
      { node := BridgeNode.character
        priority := PriorityLevel.primary
        milestone := MilestoneStatus.structured
        risk := RiskLevel.medium
        phase := TimelinePhase.now
        status := WorkPackageStatus.ready
        deliverable := "Character decomposition package" }
    primeResolved :=
      { node := BridgeNode.primeResolved
        priority := PriorityLevel.secondary
        milestone := MilestoneStatus.scaffolded
        risk := RiskLevel.high
        phase := TimelinePhase.next
        status := WorkPackageStatus.deferred
        deliverable := "Prime-resolved lifting package" }
    spectralIdentification :=
      { node := BridgeNode.spectralIdentification
        priority := PriorityLevel.terminal
        milestone := MilestoneStatus.blocked
        risk := RiskLevel.critical
        phase := TimelinePhase.blocked
        status := WorkPackageStatus.blocked
        deliverable := "Spectral identification package" }
    globalStatus := WorkPackageStatus.ready }

/-- Canonical doctrinal statement for the work-package layer. -/
theorem canonicalH7WorkPackage_doctrine :
    canonicalH7WorkPackageRecord.microlocal.status = WorkPackageStatus.blocked ∧
    canonicalH7WorkPackageRecord.character.status = WorkPackageStatus.ready ∧
    canonicalH7WorkPackageRecord.primeResolved.status = WorkPackageStatus.deferred ∧
    canonicalH7WorkPackageRecord.spectralIdentification.status = WorkPackageStatus.blocked ∧
    canonicalH7WorkPackageRecord.globalStatus = WorkPackageStatus.ready := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The work-package layer preserves the canonical timeline. -/
theorem canonicalH7WorkPackage_preserves_timeline :
    canonicalH7WorkPackageRecord.microlocal.phase = TimelinePhase.blocked ∧
    canonicalH7WorkPackageRecord.character.phase = TimelinePhase.now ∧
    canonicalH7WorkPackageRecord.primeResolved.phase = TimelinePhase.next ∧
    canonicalH7WorkPackageRecord.spectralIdentification.phase = TimelinePhase.blocked := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The work-package layer preserves the current milestone structure. -/
theorem canonicalH7WorkPackage_preserves_milestones :
    canonicalH7WorkPackageRecord.microlocal.milestone = MilestoneStatus.blocked ∧
    canonicalH7WorkPackageRecord.character.milestone = MilestoneStatus.structured ∧
    canonicalH7WorkPackageRecord.primeResolved.milestone = MilestoneStatus.scaffolded ∧
    canonicalH7WorkPackageRecord.spectralIdentification.milestone = MilestoneStatus.blocked := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The work-package layer preserves the current priority structure. -/
theorem canonicalH7WorkPackage_preserves_priorities :
    canonicalH7WorkPackageRecord.microlocal.priority = PriorityLevel.foundational ∧
    canonicalH7WorkPackageRecord.character.priority = PriorityLevel.primary ∧
    canonicalH7WorkPackageRecord.primeResolved.priority = PriorityLevel.secondary ∧
    canonicalH7WorkPackageRecord.spectralIdentification.priority = PriorityLevel.terminal := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The work-package layer preserves the current risk structure. -/
theorem canonicalH7WorkPackage_preserves_risks :
    canonicalH7WorkPackageRecord.microlocal.risk = RiskLevel.critical ∧
    canonicalH7WorkPackageRecord.character.risk = RiskLevel.medium ∧
    canonicalH7WorkPackageRecord.primeResolved.risk = RiskLevel.high ∧
    canonicalH7WorkPackageRecord.spectralIdentification.risk = RiskLevel.critical := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The character step is the first actionable package. -/
theorem canonicalH7_character_package_is_actionable :
    canonicalH7WorkPackageRecord.character.phase = TimelinePhase.now ∧
    canonicalH7WorkPackageRecord.character.status = WorkPackageStatus.ready := by
  exact ⟨rfl, rfl⟩

/-- Nonempty existence of the work-package layer. -/
theorem finite_H7WorkPackage_exists : Nonempty H7WorkPackageRecord := by
  exact ⟨canonicalH7WorkPackageRecord⟩

/-- Compact publication-style summary for the work-package layer. -/
structure BridgeWorkPackageSummary where
  noGoStatus : NoGoStatus
  globalProgramStatus : ProgramStatus
  globalMilestone : MilestoneStatus
  globalTimeline : TimelinePhase
  globalWorkStatus : WorkPackageStatus
  microlocalStatus : WorkPackageStatus
  characterStatus : WorkPackageStatus
  primeResolvedStatus : WorkPackageStatus
  spectralIdentificationStatus : WorkPackageStatus

/-- Canonical summary exported from the work-package layer. -/
def canonicalBridgeWorkPackageSummary : BridgeWorkPackageSummary :=
  { noGoStatus := canonicalBridgeTimelineSummary.noGoStatus
    globalProgramStatus := canonicalBridgeTimelineSummary.globalProgramStatus
    globalMilestone := canonicalBridgeTimelineSummary.globalMilestone
    globalTimeline := canonicalBridgeTimelineSummary.globalPhase
    globalWorkStatus := canonicalH7WorkPackageRecord.globalStatus
    microlocalStatus := canonicalH7WorkPackageRecord.microlocal.status
    characterStatus := canonicalH7WorkPackageRecord.character.status
    primeResolvedStatus := canonicalH7WorkPackageRecord.primeResolved.status
    spectralIdentificationStatus := canonicalH7WorkPackageRecord.spectralIdentification.status }

/-- Compact doctrinal theorem for the exported work-package summary. -/
theorem canonicalBridgeWorkPackageSummary_doctrine :
    canonicalBridgeWorkPackageSummary.noGoStatus = NoGoStatus.conditional ∧
    canonicalBridgeWorkPackageSummary.globalProgramStatus = ProgramStatus.candidate ∧
    canonicalBridgeWorkPackageSummary.globalMilestone = MilestoneStatus.structured ∧
    canonicalBridgeWorkPackageSummary.globalTimeline = TimelinePhase.now ∧
    canonicalBridgeWorkPackageSummary.globalWorkStatus = WorkPackageStatus.ready ∧
    canonicalBridgeWorkPackageSummary.microlocalStatus = WorkPackageStatus.blocked ∧
    canonicalBridgeWorkPackageSummary.characterStatus = WorkPackageStatus.ready ∧
    canonicalBridgeWorkPackageSummary.primeResolvedStatus = WorkPackageStatus.deferred ∧
    canonicalBridgeWorkPackageSummary.spectralIdentificationStatus = WorkPackageStatus.blocked := by
  rcases canonicalBridgeTimelineSummary_doctrine with
    ⟨hNoGo, hProg, hMil, hTime, _, _, _, _⟩
  exact ⟨
    by simpa [canonicalBridgeWorkPackageSummary] using hNoGo,
    by simpa [canonicalBridgeWorkPackageSummary] using hProg,
    by simpa [canonicalBridgeWorkPackageSummary] using hMil,
    by simpa [canonicalBridgeWorkPackageSummary] using hTime,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl
  ⟩

end H7WorkPackageProgram
end CouretUnification
