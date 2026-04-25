/-
# Meta/Layer.lean — Taxonomie des régimes de validité (v35.7)

## Doctrine

Ce fichier ne dépend de rien d'autre que du noyau Lean. Il définit les types
de stratification utilisés par tous les autres modules pour annoter leur statut
épistémique. Aucune affirmation mathématique substantielle n'y est faite.

  - Layer  : A (formel prouvé) / B (analytique conditionnel) / C (empirique) / D (spéculatif)
  - Status : grain plus fin pour le statut d'un énoncé donné
  - Statement : enregistrement annoté (titre, couche, statut, contenu)

Cette taxonomie est utilisée comme métadonnée. Elle ne contraint pas la
compilation ; elle sert de garde-fou lexical et de point d'inspection.
-/

namespace CouretUnification.Meta

/-- Régimes de validité du programme.

    | A | formel prouvé (théorème Lean fermé)
    | B | analytique conditionnel ou spécifié
    | C | empirique fort (régularité numérique reproductible)
    | D | spéculatif, philosophique ou programmatique
-/
inductive Layer where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Statut détaillé d'un énoncé. -/
inductive Status where
  | proved        -- preuve Lean complète, zéro sorry
  | encoded       -- structure encodée, contenu mathématique trivial ou différé
  | conditional   -- preuve avec sorry doctrinalement assumé
  | empirical     -- résultat numérique, non-théorème
  | speculative   -- analogie, lecture, programmatique
  deriving DecidableEq, Repr

/-- Métadonnée d'un énoncé Lean ou d'une affirmation du programme. -/
structure Statement where
  title   : String
  layer   : Layer
  status  : Status
  content : String
  deriving Repr

/-- Identité de fichier — utilisée par chaque module pour déclarer son statut.

    L'invariant `rhClaimed = false` est répliqué statiquement via
    `example : fileIdentity.rhClaimed = false := rfl` dans chaque fichier
    du noyau démonstratif. -/
structure FileIdentity where
  filename     : String
  layer        : Layer
  status       : Status
  sorryCount   : Nat
  rhClaimed    : Bool
  deriving Repr

/-- Thèse centrale du programme — niveau D (schéma unificateur, non démontré). -/
def central_thesis : Statement := {
  title := "Schéma unificateur proposé"
  layer := .D
  status := .speculative
  content :=
    "Les structures robustes émergent lorsque les niveaux topologiques, " ++
    "algébriques, métriques et épistémiques sont explicitement séparés, " ++
    "puis reconnectés par des ponts formels adaptés."
}

end CouretUnification.Meta
