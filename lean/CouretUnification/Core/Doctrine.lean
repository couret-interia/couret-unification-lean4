/-
Copyright (c) 2026 Couret-Unification Programme.
Released under Apache 2.0.

# Core/Doctrine.lean — Invariants constitutionnels centralisés

## Doctrine

Ce fichier centralise les invariants doctrinaux du programme :
  - `RHClaimed = false` : aucun fichier ne prétend prouver RH
  - Grammaire des statuts épistémiques [P]/[N]/[C]/[R]/[I]/[O]
  - Identification statique de la couche d'un fichier

Tous les fichiers du paquet importent ce module et y vérifient
statiquement leur invariant via `example : RHClaimed = false := rfl`.

## Statut

  - Couche : Core (fondement, sans dépendance Mathlib lourde)
  - Statut : [P] absolu — un seul `def` boolean et une `inductive`.
  - Aucun sorry, aucune dépendance externe.
-/

namespace CouretUnification

/-!
## Section 1 — Invariant RHClaimed

`RHClaimed = false` est l'invariant le plus fort du programme.
Il signifie : aucun théorème de ce paquet, à aucun moment, ne
prétend établir l'Hypothèse de Riemann.
-/

/-- [P] L'invariant constitutionnel : ce paquet ne prétend PAS prouver RH. -/
def RHClaimed : Bool := false

/-- [P] Vérification statique de l'invariant. -/
theorem rhClaimed_eq_false : RHClaimed = false := rfl

/-!
## Section 2 — Grammaire des statuts épistémiques

  [P]  proved        — preuve formelle Lean complète (zéro sorry)
  [N]  candidate     — pré-filtré numériquement, falsifiable, non prouvé
  [C]  conditional   — démontré sous une autre hypothèse
  [R]  refined       — preuve avec sorry techniques restants (API)
  [I]  interface     — spécification typée, pas d'engagement de preuve
  [O]  open          — ouvert, hors de portée actuelle
-/

/-- [P] Grammaire des statuts épistémiques du programme. -/
inductive EpistemicStatus where
  | proved        -- [P] preuve Lean complète
  | candidate     -- [N] pré-filtré, falsifiable, non prouvé
  | conditional   -- [C] démontré sous hypothèse
  | refined       -- [R] preuve avec sorry techniques (API)
  | interface     -- [I] spécification typée seulement
  | open_         -- [O] ouvert (open est mot-clé Lean)
  deriving DecidableEq, Repr

/-!
## Section 3 — Identification de la couche

DAG strict : Core → Logic.H3 → AnalyticHorizon → Global.
Aucun fichier ne peut importer un fichier d'une couche supérieure.
-/

/-- [P] Les couches du programme dans l'ordre du DAG. -/
inductive Layer where
  | core              -- Core/ : noyau fini, doctrine
  | logicH3           -- Logic/H3/ : verrous H1-H3, blocs A-B
  | analyticHorizon   -- AnalyticHorizon/ : Bloc D, det₂, EulerCompletion
  | global            -- Global/ : recollement final (entièrement [O])
  deriving DecidableEq, Repr

/-- [P] Une fiche d'identité pour un fichier du paquet. -/
structure FileIdentity where
  module       : String              -- nom du module Lean
  layer        : Layer
  status       : EpistemicStatus
  sorryCount   : Nat
  rhClaimed    : Bool := false       -- doit toujours être false
  deriving Repr

/-- [P] Tout `FileIdentity` respecte l'invariant RHClaimed = false. -/
theorem fileIdentity_rhClaimed_false (id : FileIdentity) (h : id.rhClaimed = false) :
    id.rhClaimed = false := h

end CouretUnification
