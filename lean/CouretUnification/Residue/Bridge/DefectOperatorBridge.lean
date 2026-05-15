/-
  CouretUnification.Residue.Bridge.DefectOperatorBridge

  Pont explicite entre la structure finie ponctuée côté Residue
  et l'interface matricielle DefectOperator30 côté AnalyticHorizon.

  Rôle :
  - exposer uniquement les objets résiduels nécessaires à DefectOperator30 ;
  - rendre visible la promotion Residue → AnalyticHorizon ;
  - satisfaire le gate no-frozen-imports par contrat explicite.

  Ce fichier ne doit importer aucune couche analytique.
-/

import CouretUnification.Residue.PuncturedKlein30

namespace CouretUnification.Residue.Bridge

/-- Type résiduel exposé au défaut matriciel. -/
abbrev DefectOperatorZ30 := CouretUnification.Residue.Z30

/-- Triangle corrigé exposé au défaut matriciel. -/
def defectOperatorTC : Finset DefectOperatorZ30 :=
  CouretUnification.Residue.TC

/-- Élément fantôme exposé au défaut matriciel. -/
def defectOperatorPhantom19 : DefectOperatorZ30 :=
  CouretUnification.Residue.Phantom19

/-- Sous-structure K₄ exposée au défaut matriciel. -/
def defectOperatorK4 : Finset DefectOperatorZ30 :=
  CouretUnification.Residue.K4

/-- Marqueur de contrat : le pont DefectOperator est chargé. -/
def defectOperatorBridgeLoaded : Bool := true

end CouretUnification.Residue.Bridge
