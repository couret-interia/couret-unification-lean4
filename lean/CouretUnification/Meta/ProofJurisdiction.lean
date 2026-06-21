/-
  Couret-Unification — v35.9.1
  Meta/ProofJurisdiction.lean

  Objet : juridiction de preuve. No Certificate ⇒ No Claim.

  Statut     : Frozen-eligible (identique à v35.9.0)
  RHClaimed              : false (vérifié par frozen_no_rh_claim)
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0
  localConstants         : 0

  Pour Bernard.
-/

namespace CouretUnification.Meta

inductive ClaimStatus where
  | proved
  | definitionalClosed
  | conditional
  | specOnly
  | openProblem
  | falsified
  | retiredArtifact
deriving DecidableEq, Repr

structure ClaimGate where
  name             : String
  status           : ClaimStatus
  sorryCount       : Nat
  rhClaimed        : Bool
  hpClaimed        : Bool
  physicalClaimed  : Bool

def admissibleToFrozen (c : ClaimGate) : Prop :=
  (c.status = ClaimStatus.proved ∨ c.status = ClaimStatus.definitionalClosed)
  ∧ c.sorryCount = 0
  ∧ c.rhClaimed = false
  ∧ c.hpClaimed = false
  ∧ c.physicalClaimed = false

def activeButNotClaimed (c : ClaimGate) : Prop :=
  c.status = ClaimStatus.conditional
  ∨ c.status = ClaimStatus.specOnly
  ∨ c.status = ClaimStatus.openProblem

def inhibited (c : ClaimGate) : Prop :=
  c.status = ClaimStatus.falsified
  ∨ c.status = ClaimStatus.retiredArtifact

theorem frozen_no_rh_claim
    (c : ClaimGate) (h : admissibleToFrozen c) :
    c.rhClaimed = false := h.2.2.1

theorem frozen_no_hp_claim
    (c : ClaimGate) (h : admissibleToFrozen c) :
    c.hpClaimed = false := h.2.2.2.1

theorem frozen_no_physical_claim
    (c : ClaimGate) (h : admissibleToFrozen c) :
    c.physicalClaimed = false := h.2.2.2.2

theorem frozen_zero_sorry
    (c : ClaimGate) (h : admissibleToFrozen c) :
    c.sorryCount = 0 := h.2.1

theorem inhibited_not_admissible
    (c : ClaimGate) (h : inhibited c) :
    ¬ admissibleToFrozen c := by
  intro hadm
  rcases h with hf | hr
  · rcases hadm.1 with hp | hd
    · rw [hf] at hp; cases hp
    · rw [hf] at hd; cases hd
  · rcases hadm.1 with hp | hd
    · rw [hr] at hp; cases hp
    · rw [hr] at hd; cases hd

end CouretUnification.Meta
