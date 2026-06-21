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

/-- Statut à cinq niveaux pour les ponts analytiques dans le programme. -/
inductive BridgeStatus where
  | absent
  | candidate
  | conditional
  | theoremTarget
  | closed
deriving Repr, DecidableEq, Inhabited

end CouretUnification.EpistemicDiscipline

-- Réexporter dans l'espace de noms supérieur pour faciliter la lecture en aval.
export CouretUnification.EpistemicDiscipline (BridgeStatus)
