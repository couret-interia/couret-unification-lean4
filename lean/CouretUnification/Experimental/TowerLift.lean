/-
# CouretUnification.Experimental.TowerLift

Ombrelle expérimentale TowerLift.

Ces modules contiennent des modèles jouets, des calculs flottants et des
vérifications exécutables par `#eval`. Ils sont utiles pour la reproductibilité
et l'exploration, mais ne constituent pas le noyau démonstratif `[D]`.
-/

import CouretUnification.Experimental.TowerLift.ToyModelSpec
import CouretUnification.Experimental.TowerLift.ToyModel
import CouretUnification.Experimental.TowerLift.ToyModelFloat

namespace CouretUnification.Experimental.TowerLift

def loaded : Bool := true

def status : String :=
  "[Experimental] toy models and executable numerical checks"

end CouretUnification.Experimental.TowerLift
