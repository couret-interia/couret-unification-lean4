/-
  Couret-Unification — v35.9.0
  Meta/ProofJurisdiction.lean

  Objet : juridiction de preuve. Formalise la règle FCI :

           No Certificate  ⇒  No Claim.

  Statut     : Frozen-eligible (0 sorry, 0 axiome local, structures pures)
  Layer      : Meta (aucune dépendance amont dans CouretUnification)
  Doctrine   : carte de promotion Active → Frozen
  RHClaimed              : false (vérifié par frozen_no_rh_claim)
  HilbertPolyaClaimed    : false (vérifié par frozen_no_hp_claim)
  PhysicalClaimed        : false (vérifié par frozen_no_physical_claim)
  sorryCount             : 0
  axiomCount             : 0

  Règle architecturale stricte :
    Frozen = 0 sorry + 0 axiome local non autorisé + 0 RH/HP/Physical claim.

    La rupture d'un seul de ces invariants suffit à inhiber la promotion.

  Historique des versions :
    v35.9-pre : première rédaction (Float comme placeholder pour ℂ).
    v35.9.0   : aucune modification — ce module était déjà robuste.

  Pour Bernard.
-/

namespace CouretUnification.Meta

/- ═══════════════════════════════════════════════════════════════════════════
   STATUT D'UN CLAIM
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Statut épistémique d'un claim dans le programme. -/
inductive ClaimStatus where
  | proved
  | definitionalClosed
  | conditional
  | specOnly
  | openProblem
  | falsified
  | retiredArtifact
deriving DecidableEq, Repr

/- ═══════════════════════════════════════════════════════════════════════════
   CLAIMGATE : LE PORTAIL DE PROMOTION
   ═══════════════════════════════════════════════════════════════════════════ -/

structure ClaimGate where
  name             : String
  status           : ClaimStatus
  sorryCount       : Nat
  rhClaimed        : Bool
  hpClaimed        : Bool
  physicalClaimed  : Bool

/- ═══════════════════════════════════════════════════════════════════════════
   ADMISSIBILITÉ DE PROMOTION
   ═══════════════════════════════════════════════════════════════════════════ -/

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

/- ═══════════════════════════════════════════════════════════════════════════
   THÉORÈMES DE JURIDICTION
   ═══════════════════════════════════════════════════════════════════════════ -/

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
