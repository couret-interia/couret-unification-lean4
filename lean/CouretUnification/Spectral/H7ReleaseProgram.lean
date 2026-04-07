import CouretUnification.Spectral.H7SignoffProgram

namespace CouretUnification
namespace H7ReleaseProgram

open H6NoGo
open H7BridgeProgram
open H7MilestoneProgram
open H7TimelineProgram
open H7WorkPackageProgram
open H7AcceptanceProgram
open H7EvidenceProgram
open H7AuditProgram
open H7SignoffProgram

inductive ReleaseStatus where
  | blocked
  | pending
  | staged
  | releasable
  | released
deriving DecidableEq, Repr

structure ReleaseDescriptor where
  auditStatus : AuditStatus
  evidenceKind : EvidenceKind
  approved : Bool
  releaseNotePresent : Bool
  status : ReleaseStatus

structure H7ReleaseRecord where
  signoff : H7SignoffRecord
  microlocal : ReleaseDescriptor
  character : ReleaseDescriptor
  primeResolved : ReleaseDescriptor
  spectralIdentification : ReleaseDescriptor
  globalReleased : Bool
  globalStatus : ReleaseStatus

def canonicalH7ReleaseRecord : H7ReleaseRecord where
  signoff := canonicalH7SignoffRecord
  microlocal :=
    { auditStatus := canonicalH7SignoffRecord.microlocal.auditStatus
      evidenceKind := canonicalH7SignoffRecord.microlocal.evidenceKind
      approved := false
      releaseNotePresent := false
      status := ReleaseStatus.blocked }
  character :=
    { auditStatus := canonicalH7SignoffRecord.character.auditStatus
      evidenceKind := canonicalH7SignoffRecord.character.evidenceKind
      approved := canonicalH7SignoffRecord.character.approved
      releaseNotePresent := true
      status := ReleaseStatus.releasable }
  primeResolved :=
    { auditStatus := canonicalH7SignoffRecord.primeResolved.auditStatus
      evidenceKind := canonicalH7SignoffRecord.primeResolved.evidenceKind
      approved := false
      releaseNotePresent := false
      status := ReleaseStatus.staged }
  spectralIdentification :=
    { auditStatus := canonicalH7SignoffRecord.spectralIdentification.auditStatus
      evidenceKind := canonicalH7SignoffRecord.spectralIdentification.evidenceKind
      approved := false
      releaseNotePresent := false
      status := ReleaseStatus.blocked }
  globalReleased := false
  globalStatus := ReleaseStatus.pending

theorem canonicalH7Release_doctrine :
    canonicalH7ReleaseRecord.microlocal.status = ReleaseStatus.blocked ∧
    canonicalH7ReleaseRecord.character.status = ReleaseStatus.releasable ∧
    canonicalH7ReleaseRecord.primeResolved.status = ReleaseStatus.staged ∧
    canonicalH7ReleaseRecord.spectralIdentification.status = ReleaseStatus.blocked ∧
    canonicalH7ReleaseRecord.character.approved = true ∧
    canonicalH7ReleaseRecord.character.releaseNotePresent = true ∧
    canonicalH7ReleaseRecord.globalReleased = false ∧
    canonicalH7ReleaseRecord.globalStatus = ReleaseStatus.pending := by
  decide

theorem canonicalH7Release_preserves_signoff :
    canonicalH7ReleaseRecord.signoff.microlocal.status = SignoffStatus.blocked ∧
    canonicalH7ReleaseRecord.signoff.character.status = SignoffStatus.approved ∧
    canonicalH7ReleaseRecord.signoff.primeResolved.status = SignoffStatus.pending ∧
    canonicalH7ReleaseRecord.signoff.spectralIdentification.status = SignoffStatus.blocked := by
  decide

theorem canonicalH7_character_release_is_releasable :
    canonicalH7ReleaseRecord.character.auditStatus = AuditStatus.reviewed ∧
    canonicalH7ReleaseRecord.character.evidenceKind = EvidenceKind.structuralRecord ∧
    canonicalH7ReleaseRecord.character.approved = true ∧
    canonicalH7ReleaseRecord.character.status = ReleaseStatus.releasable ∧
    canonicalH7ReleaseRecord.character.releaseNotePresent = true := by
  decide

theorem finite_H7Release_exists : Nonempty H7ReleaseRecord :=
  ⟨canonicalH7ReleaseRecord⟩

structure BridgeReleaseSummary where
  noGoStatus : NoGoStatus
  globalProgramStatus : ProgramStatus
  globalMilestone : MilestoneStatus
  globalTimeline : TimelinePhase
  globalWorkStatus : WorkPackageStatus
  globalAcceptanceStatus : AcceptanceStatus
  globalCertified : Bool
  globalAuditStatus : AuditStatus
  globalApproved : Bool
  globalReleased : Bool
  globalReleaseStatus : ReleaseStatus
  microlocalReleaseStatus : ReleaseStatus
  characterReleaseStatus : ReleaseStatus
  primeResolvedReleaseStatus : ReleaseStatus
  spectralIdentificationReleaseStatus : ReleaseStatus
  characterReleasable : Bool

def canonicalBridgeReleaseSummary : BridgeReleaseSummary where
  noGoStatus := canonicalBridgeSignoffSummary.noGoStatus
  globalProgramStatus := canonicalBridgeSignoffSummary.globalProgramStatus
  globalMilestone := canonicalBridgeSignoffSummary.globalMilestone
  globalTimeline := canonicalBridgeSignoffSummary.globalTimeline
  globalWorkStatus := canonicalBridgeSignoffSummary.globalWorkStatus
  globalAcceptanceStatus := canonicalBridgeSignoffSummary.globalAcceptanceStatus
  globalCertified := canonicalBridgeSignoffSummary.globalCertified
  globalAuditStatus := canonicalBridgeSignoffSummary.globalAuditStatus
  globalApproved := canonicalBridgeSignoffSummary.globalApproved
  globalReleased := canonicalH7ReleaseRecord.globalReleased
  globalReleaseStatus := canonicalH7ReleaseRecord.globalStatus
  microlocalReleaseStatus := canonicalH7ReleaseRecord.microlocal.status
  characterReleaseStatus := canonicalH7ReleaseRecord.character.status
  primeResolvedReleaseStatus := canonicalH7ReleaseRecord.primeResolved.status
  spectralIdentificationReleaseStatus := canonicalH7ReleaseRecord.spectralIdentification.status
  characterReleasable := true

theorem canonicalBridgeReleaseSummary_doctrine :
    canonicalBridgeReleaseSummary.noGoStatus = NoGoStatus.conditional ∧
    canonicalBridgeReleaseSummary.globalProgramStatus = ProgramStatus.candidate ∧
    canonicalBridgeReleaseSummary.globalMilestone = MilestoneStatus.structured ∧
    canonicalBridgeReleaseSummary.globalTimeline = TimelinePhase.now ∧
    canonicalBridgeReleaseSummary.globalWorkStatus = WorkPackageStatus.ready ∧
    canonicalBridgeReleaseSummary.globalAcceptanceStatus = AcceptanceStatus.pending ∧
    canonicalBridgeReleaseSummary.globalCertified = false ∧
    canonicalBridgeReleaseSummary.globalAuditStatus = AuditStatus.pending ∧
    canonicalBridgeReleaseSummary.globalApproved = false ∧
    canonicalBridgeReleaseSummary.globalReleased = false ∧
    canonicalBridgeReleaseSummary.globalReleaseStatus = ReleaseStatus.pending ∧
    canonicalBridgeReleaseSummary.microlocalReleaseStatus = ReleaseStatus.blocked ∧
    canonicalBridgeReleaseSummary.characterReleaseStatus = ReleaseStatus.releasable ∧
    canonicalBridgeReleaseSummary.primeResolvedReleaseStatus = ReleaseStatus.staged ∧
    canonicalBridgeReleaseSummary.spectralIdentificationReleaseStatus = ReleaseStatus.blocked ∧
    canonicalBridgeReleaseSummary.characterReleasable = true := by
  decide

namespace FiniteDoctrine

theorem character_release_releasable :
    canonicalH7ReleaseRecord.character.status = ReleaseStatus.releasable := by
  decide

theorem global_release_pending :
    canonicalH7ReleaseRecord.globalStatus = ReleaseStatus.pending := by
  decide

theorem global_release_not_released :
    canonicalH7ReleaseRecord.globalReleased = false := by
  decide

theorem release_summary :
    canonicalBridgeReleaseSummary.globalReleaseStatus = ReleaseStatus.pending ∧
    canonicalBridgeReleaseSummary.characterReleaseStatus = ReleaseStatus.releasable ∧
    canonicalBridgeReleaseSummary.characterReleasable = true := by
  decide

end FiniteDoctrine

end H7ReleaseProgram
end CouretUnification
