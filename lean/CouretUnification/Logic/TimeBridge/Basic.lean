/-
  Couret-Unification — v35.8.8
  Logic/TimeBridge/Basic.lean

  Objet : socle commun de la chaîne TimeBridge.

         Définit les types et conventions partagés par les fichiers
         spécification du registre temporel (R3-Modulaire, R4-DBM,
         R1-Spectral) :

           - OpenProblem : type de consignation des questions ouvertes
                          du programme, avec registre et statut typés.

         Aucun théorème analytique. Aucun sorry. Aucun import lourd.

  Statut     : SPEC ONLY — fondation typée pour la chaîne TimeBridge
  Layer      : Platinum (Specification)
  Doctrine   : socle commun TimeBridge
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  sorryCount             : 0

  Pour Bernard.
-/

namespace CouretUnification.Logic.TimeBridge

/- ═══════════════════════════════════════════════════════════════════════════
   TYPE OpenProblem
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Type de consignation d'une question ouverte du programme.

    Une `OpenProblem P` est un *enregistrement typé* de l'état d'une
    question ouverte : son emplacement dans le registre programmatique
    (`registry`) et son statut narratif (`status`).

    Le paramètre `P : Prop` accompagne la consignation pour permettre,
    le cas échéant, de typer la propriété mathématique elle-même.
    Dans la pratique courante de la chaîne TimeBridge, on l'instancie
    avec `True` car la consignation joue un rôle documentaire, pas
    démonstratif : la véritable propriété ouverte n'est pas démontrée
    ici, elle est seulement *nommée*.

    Exemple d'usage typique :

        def my_open_question : OpenProblem True := {
          registry := "R3-Modulaire / B1"
          status   := "ouvert — cible du programme"
        }

    Cette construction n'invoque ni axiome ni `sorry`. Elle ne prétend
    pas démontrer `P`. Elle consigne une question ouverte sous une
    forme typée, auditable, et compilable.

    Doctrine : un `OpenProblem` est un acte de nomination, pas une
    preuve. Il appartient à la couche Active du programme, jamais à
    la couche Frozen. -/
structure OpenProblem (P : Prop) where
  /-- Emplacement dans le registre programmatique (e.g. "R3-Modulaire / B1"). -/
  registry : String
  /-- Statut narratif de la question (e.g. "ouvert", "partiel", "conjectural"). -/
  status   : String

end CouretUnification.Logic.TimeBridge