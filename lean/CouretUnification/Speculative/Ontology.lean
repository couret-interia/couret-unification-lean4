/-
# Speculative/Ontology.lean — Lectures ontologiques computationnelles (v35.7)

## Statut épistémique

  - Couche : Speculative
  - Statut : [D] speculative
  - sorryCount : 0
  - RHClaimed = false
  - **Ce fichier n'est jamais importé par Logic/ ni par Empirical/.**

## Doctrine

Ce fichier référence — sans les endosser — certaines lectures ontologiques
ou cosmologiques évoquées dans des échanges périphériques au programme
(NRHF, « verbes gelés », computationnalité sans substrat).

Ces propositions peuvent fournir un vocabulaire heuristique pour penser
la stabilité, la récursion ou la fixation de processus. Elles ne sont pas
des résultats du programme. Elles sont enregistrées ici pour traçabilité.

Aucun contenu mathématique substantiel n'y est défini.
-/

import CouretUnification.Meta.Layer

namespace CouretUnification
namespace Speculative
namespace Ontology

open CouretUnification.Meta

def nrhf_reference : Statement := {
  title := "Cadre Nexus / NRHF"
  layer := .D
  status := .speculative
  content :=
    "Lecture ontologique computationnelle proposée dans certains échanges " ++
    "périphériques. Ne fait pas partie du noyau démonstratif et n'est " ++
    "ni endossée ni utilisée par le programme."
}

def frozen_verbs_reference : Statement := {
  title := "Métaphore des « verbes gelés »"
  layer := .D
  status := .speculative
  content :=
    "Image suggérant que les structures stables seraient des résidus de " ++
    "processus récursifs. Métaphore heuristique uniquement."
}

def fileIdentity : FileIdentity := {
  filename := "Speculative/Ontology.lean"
  layer := .D
  status := .speculative
  sorryCount := 0
  rhClaimed := false
}

example : fileIdentity.rhClaimed = false := rfl
example : fileIdentity.layer = .D := rfl

end Ontology
end Speculative
end CouretUnification
