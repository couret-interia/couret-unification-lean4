/-
# CouretUnification/Meta/Doctrine.lean — Couche doctrinale (v35.8.3)

## Statut
  - Couche : Meta
  - Sorry : 0
  - RHClaimed = false

## Rôle

Ce fichier fournit :
  1. Les types minimaux pour l'identité doctrinale (Layer, Status, FileIdentity).
  2. Les types pour les verrous ouverts (OpenLock, LockStatus).
  3. L'invariant global RHClaimed = false au niveau du projet.

Pas de contenu mathématique.
-/

namespace CouretUnification
namespace Meta

/-! ## Section 1 — Couches architecturales -/

inductive Layer where
  | A  -- noyau fini, combinatoire, algébrique certifié (FiniteCore)
  | B  -- analyse conditionnelle, verrous localisés (Logic)
  | C  -- mur terminal, rh_wall (H3/L12)
  deriving Repr, DecidableEq, Inhabited

/-! ## Section 2 — Statuts de fichier -/

inductive Status where
  | certified     -- prouvé sans sorry ni axiome local
  | conditional   -- dépend d'hypothèses explicites, non encore prouvées
  | open_         -- verrou ouvert, stratégie identifiée
  | nogo          -- théorème d'obstruction négative
  | rh_wall       -- mur terminal équivalent à RH
  deriving Repr, DecidableEq, Inhabited

/-! ## Section 3 — Identité de fichier -/

structure FileIdentity where
  filename   : String
  layer      : Layer
  status     : Status
  sorryCount : Nat
  rhClaimed  : Bool := false
  deriving Repr

/-- Invariant doctrinal : aucun fichier ne prétend prouver RH. -/
def FileIdentity.invariantRHClaimed (fi : FileIdentity) : Prop :=
  fi.rhClaimed = false

/-- Un fichier est propre s'il est certifié et ne revendique pas RH. -/
def FileIdentity.isClean (fi : FileIdentity) : Bool :=
  match fi.status with
  | .certified => fi.sorryCount == 0 && !fi.rhClaimed
  | _ => false

/-! ## Section 4 — Types pour les verrous -/

inductive LockStatus where
  | closed        -- verrou fermé
  | conditional   -- fermé modulo hypothèses
  | open_         -- ouvert, travail en cours
  | nogo          -- obstruction prouvée
  | rh_wall       -- mur terminal
  deriving Repr, DecidableEq, Inhabited

structure OpenLock where
  identifier        : String
  shortDescription  : String
  status            : LockStatus
  strategyClaimed   : Option String := none
  formallyProved    : Bool := false
  notes             : String := ""
  deriving Repr

/-! ## Section 5 — Invariant global du projet -/

/-- Invariant projet : la liste de tous les verrous doit respecter
    `formallyProved = false` tant que le fichier prétend traiter RH.
    Ceci encode doctrinalement : aucun verrou de type `rh_wall` ne peut
    être marqué comme prouvé. -/
def OpenLock.rhWallInvariant (l : OpenLock) : Prop :=
  l.status = LockStatus.rh_wall → l.formallyProved = false

theorem rhWallInvariant_default (id desc : String) (notes : String) :
    (OpenLock.rhWallInvariant
      { identifier := id, shortDescription := desc
        status := LockStatus.rh_wall, strategyClaimed := none
        formallyProved := false, notes := notes }) := by
  intro _; rfl

end Meta
end CouretUnification
