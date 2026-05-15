/-
  CouretUnification.EpistemicDiscipline.BridgeStatus
  ════════════════════════════════════════════════════════════════════
  Statut épistémique des ponts analytiques du programme.

  Cinq niveaux distinguent les degrés d'engagement :
    • absent         — pont non encore identifié, hors corpus
    • candidate      — pont identifié, conjectural, sans cible formelle
    • conditional    — pont prouvé conditionnellement à un autre lock
    • theoremTarget  — pont avec cible formelle, en cours de fermeture
    • closed         — pont fermé, sans sorry, sans condition

  Doctrine : v38 unifiée
-/

namespace CouretUnification.EpistemicDiscipline

/-- Five-level status for analytic bridges in the program. -/
inductive BridgeStatus where
  | absent
  | candidate
  | conditional
  | theoremTarget
  | closed
deriving Repr, DecidableEq, Inhabited

end CouretUnification.EpistemicDiscipline

-- Re-export at the top namespace for downstream readability.
export CouretUnification.EpistemicDiscipline (BridgeStatus)
