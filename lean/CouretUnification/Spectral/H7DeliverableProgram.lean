import CouretUnification.Spectral.H7WorkPackageProgram

namespace CouretUnification
namespace H7DeliverableProgram

open H6NoGo
open H7BridgeProgram
open H7MilestoneProgram
open H7TimelineProgram
open H7WorkPackageProgram

/-- Kind of concrete artifact expected from a work package. -/
inductive DeliverableKind where
  | lemmaPack
  | decompositionFile
  | liftingPrototype
  | obstructionNote
deriving DecidableEq, Repr

/-- Concrete deliverable attached to one work package. -/
structure DeliverablePackage where
  work : WorkPackage
  kind : DeliverableKind
  acceptanceReady : Bool
  artifactName : String

/-- H7.7 layer: explicit deliverable packaging of the work-package programme. -/
structure H7DeliverableRecord where
  workPackage : H7WorkPackageRecord
  microlocal : DeliverablePackage
  character : DeliverablePackage
  primeResolved : DeliverablePackage
  spectralIdentification : DeliverablePackage
  globalAcceptanceReady : Bool

/-- Canonical deliverable layer extracted from the work-package programme. -/
def canonicalH7DeliverableRecord : H7DeliverableRecord :=
  { workPackage := canonicalH7WorkPackageRecord
    microlocal :=
      { work := canonicalH7WorkPackageRecord.microlocal
        kind := DeliverableKind.obstructionNote
        acceptanceReady := false
        artifactName := "microlocal_obstruction_note" }
    character :=
      { work := canonicalH7WorkPackageRecord.character
        kind := DeliverableKind.decompositionFile
        acceptanceReady := true
        artifactName := "character_decomposition_package" }
    primeResolved :=
      { work := canonicalH7WorkPackageRecord.primeResolved
        kind := DeliverableKind.liftingPrototype
        acceptanceReady := false
        artifactName := "prime_resolved_lifting_prototype" }
    spectralIdentification :=
      { work := canonicalH7WorkPackageRecord.spectralIdentification
        kind := DeliverableKind.lemmaPack
        acceptanceReady := false
        artifactName := "spectral_identification_obstruction_pack" }
    globalAcceptanceReady := false }

/-- Canonical doctrinal statement for the deliverable layer. -/
theorem canonicalH7Deliverable_doctrine :
    canonicalH7DeliverableRecord.microlocal.kind = DeliverableKind.obstructionNote ∧
    canonicalH7DeliverableRecord.character.kind = DeliverableKind.decompositionFile ∧
    canonicalH7DeliverableRecord.primeResolved.kind = DeliverableKind.liftingPrototype ∧
    canonicalH7DeliverableRecord.spectralIdentification.kind = DeliverableKind.lemmaPack ∧
    canonicalH7DeliverableRecord.character.acceptanceReady = true ∧
    canonicalH7DeliverableRecord.globalAcceptanceReady = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The deliverable layer preserves the work-package statuses. -/
theorem canonicalH7Deliverable_preserves_work_status :
    canonicalH7DeliverableRecord.microlocal.work.status = WorkPackageStatus.blocked ∧
    canonicalH7DeliverableRecord.character.work.status = WorkPackageStatus.ready ∧
    canonicalH7DeliverableRecord.primeResolved.work.status = WorkPackageStatus.deferred ∧
    canonicalH7DeliverableRecord.spectralIdentification.work.status = WorkPackageStatus.blocked := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The character package remains the first acceptance-ready deliverable. -/
theorem canonicalH7_character_deliverable_is_ready :
    canonicalH7DeliverableRecord.character.work.status = WorkPackageStatus.ready ∧
    canonicalH7DeliverableRecord.character.acceptanceReady = true := by
  exact ⟨rfl, rfl⟩

/-- Nonempty existence of the deliverable layer. -/
theorem finite_H7Deliverable_exists : Nonempty H7DeliverableRecord := by
  exact ⟨canonicalH7DeliverableRecord⟩

/-- Compact publication-style summary for the deliverable layer. -/
structure BridgeDeliverableSummary where
  noGoStatus : NoGoStatus
  globalProgramStatus : ProgramStatus
  globalMilestone : MilestoneStatus
  globalTimeline : TimelinePhase
  globalWorkStatus : WorkPackageStatus
  globalAcceptanceReady : Bool
  microlocalKind : DeliverableKind
  characterKind : DeliverableKind
  primeResolvedKind : DeliverableKind
  spectralIdentificationKind : DeliverableKind
  characterAcceptanceReady : Bool

/-- Canonical summary exported from the deliverable layer. -/
def canonicalBridgeDeliverableSummary : BridgeDeliverableSummary :=
  { noGoStatus := canonicalBridgeWorkPackageSummary.noGoStatus
    globalProgramStatus := canonicalBridgeWorkPackageSummary.globalProgramStatus
    globalMilestone := canonicalBridgeWorkPackageSummary.globalMilestone
    globalTimeline := canonicalBridgeWorkPackageSummary.globalTimeline
    globalWorkStatus := canonicalBridgeWorkPackageSummary.globalWorkStatus
    globalAcceptanceReady := canonicalH7DeliverableRecord.globalAcceptanceReady
    microlocalKind := canonicalH7DeliverableRecord.microlocal.kind
    characterKind := canonicalH7DeliverableRecord.character.kind
    primeResolvedKind := canonicalH7DeliverableRecord.primeResolved.kind
    spectralIdentificationKind := canonicalH7DeliverableRecord.spectralIdentification.kind
    characterAcceptanceReady := canonicalH7DeliverableRecord.character.acceptanceReady }

/-- Compact doctrinal theorem for the exported deliverable summary. -/
theorem canonicalBridgeDeliverableSummary_doctrine :
    canonicalBridgeDeliverableSummary.noGoStatus = NoGoStatus.conditional ∧
    canonicalBridgeDeliverableSummary.globalProgramStatus = ProgramStatus.candidate ∧
    canonicalBridgeDeliverableSummary.globalMilestone = MilestoneStatus.structured ∧
    canonicalBridgeDeliverableSummary.globalTimeline = TimelinePhase.now ∧
    canonicalBridgeDeliverableSummary.globalWorkStatus = WorkPackageStatus.ready ∧
    canonicalBridgeDeliverableSummary.globalAcceptanceReady = false ∧
    canonicalBridgeDeliverableSummary.microlocalKind = DeliverableKind.obstructionNote ∧
    canonicalBridgeDeliverableSummary.characterKind = DeliverableKind.decompositionFile ∧
    canonicalBridgeDeliverableSummary.primeResolvedKind = DeliverableKind.liftingPrototype ∧
    canonicalBridgeDeliverableSummary.spectralIdentificationKind = DeliverableKind.lemmaPack ∧
    canonicalBridgeDeliverableSummary.characterAcceptanceReady = true := by
  rcases canonicalBridgeWorkPackageSummary_doctrine with
    ⟨hNoGo, hProg, hMil, hTime, hWork, _, _, _, _⟩
  exact ⟨
    by simpa [canonicalBridgeDeliverableSummary] using hNoGo,
    by simpa [canonicalBridgeDeliverableSummary] using hProg,
    by simpa [canonicalBridgeDeliverableSummary] using hMil,
    by simpa [canonicalBridgeDeliverableSummary] using hTime,
    by simpa [canonicalBridgeDeliverableSummary] using hWork,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl
  ⟩

end H7DeliverableProgram
end CouretUnification
