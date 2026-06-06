/-
# CouretUnification.Experimental.TowerLift

Ombrelle expérimentale TowerLift.

Ces modules contiennent des modèles jouets, des calculs flottants et des
vérifications exécutables par `#eval`. Ils sont utiles pour la reproductibilité
et l'exploration, mais ne constituent pas le noyau démonstratif `[D]`.
-/

import CouretUnification.Experimental.TowerLift.ToyModelSpec
-- import CouretUnification.Experimental.TowerLift.ToyModel      -- Attic v38.4.17
-- import CouretUnification.Experimental.TowerLift.ToyModelFloat -- Attic v38.4.17

namespace CouretUnification.Experimental.TowerLift

/-- Drapeau minimal indiquant que l’ombrelle expérimentale TowerLift est chargée. -/
def loaded : Bool := true

/-- Statut doctrinal de cette ombrelle : expérimental, non démonstratif `[D]`. -/
def status : String := "[Experimental] toy models and executable numerical checks"

end CouretUnification.Experimental.TowerLift
