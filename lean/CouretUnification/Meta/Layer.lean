/-
# Meta/Layer.lean — Taxonomie des régimes de validité (v35.7, étendu v38)

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

inductive Layer where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Statut détaillé d'un énoncé.

    v38 : ajout de `nogo` et `definitional` (anciennement dans Meta/Doctrine).
    `Doctrine.lean` est désormais une façade qui ne déclare plus
    de doublon `Status` ni `Layer`. -/
inductive Status where
  | proved
  | encoded
  | conditional
  | empirical
  | speculative
  | nogo          -- théorème d'obstruction (no-go)
  | definitional  -- chantier amont de définitions effectives
  deriving DecidableEq, Repr

structure Statement where
  title   : String
  layer   : Layer
  status  : Status
  content : String
  deriving Repr

structure FileIdentity where
  filename     : String
  layer        : Layer
  status       : Status
  sorryCount   : Nat
  rhClaimed    : Bool
  deriving Repr

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
