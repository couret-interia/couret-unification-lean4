/-
  CouretUnification.Logic.ExplicitFormula.ArchimedeanKernelBound
  ════════════════════════════════════════════════════════════════════
  Interface typée pour le noyau archimédien de la formule explicite.

  Ce fichier ne construit pas encore le vrai noyau digamma/Gamma.
  Il fournit seulement une structure abstraite permettant d'enregistrer :

    • un noyau archimédien `K : ℝ → ℂ` ;
    • une obligation de croissance logarithmique ;
    • un côté archimédien typé comme `FormulaSide` ;
    • une obligation d'intégrabilité.

  Doctrine Frozen / Active
  ------------------------
  Dans la couche Frozen, le noyau archimédien reste abstrait.
  L'instanciation réelle par le noyau digamma/Gamma appartient à une
  couche Active ultérieure, où les hypothèses analytiques devront être
  formulées et prouvées explicitement.

  Garde-fous
  ----------
  • aucun noyau digamma/Gamma concret n'est construit ici ;
  • aucune borne archimédienne réelle n'est prouvée ici ;
  • aucune intégrabilité analytique n'est démontrée ici ;
  • aucune formule explicite globale n'est fermée ici ;
  • aucune conséquence RH n'est exportée.

  Statut
  ------
  Interface logique / Frozen-safe.
  Obligations typées, non fermées analytiquement.
-/

import CouretUnification.Logic.ExplicitFormula.TraceObject

namespace CouretUnification.Logic.ExplicitFormula

/--
Noyau archimédien abstrait.

Dans la couche Frozen, ce n'est pas encore le noyau digamma.
C'est un noyau paramétré muni d'une obligation de croissance.
-/
structure ArchimedeanKernel where
  K : ℝ → ℂ
  logarithmicGrowth : Prop

/--
Côté archimédien comme donnée typée.

L'instanciation réelle digamma/Gamma appartient à la couche Active,
non à la couche Frozen.
-/
structure ArchimedeanSide where
  kernel : ArchimedeanKernel
  side : FormulaSide
  integrabilityObligation : Prop

end CouretUnification.Logic.ExplicitFormula
