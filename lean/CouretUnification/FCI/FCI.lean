/-
================================================================================
  FCI/FCI.lean
================================================================================
  Programme Couret-Unification · Couche FCI
  Cible effective : Lean 4.29.1 / Mathlib4

  Façade publique de la couche Fail-Close Integrity.

  Cette façade regroupe les modules FCI actuellement fermés :

    - ModThirtyChecker
    - ModThirtyCheckerBridge
    - CausalSupportImmunity
    - CausalSupportMeasureBridge

  Statut v38 :
    - sorry/admit : 0 dans lean/CouretUnification/FCI
    - build local : PASS
    - All.lean    : PASS
    - RHClaimed   : false
-/

import CouretUnification.FCI.ModThirtyChecker
import CouretUnification.FCI.ModThirtyCheckerBridge
import CouretUnification.FCI.CausalSupportImmunity
import CouretUnification.FCI.CausalSupportMeasureBridge

namespace FCI

/--
Marqueur structurel : la façade FCI est chargée.

Ce théorème n'ajoute aucun contenu mathématique ; il sert de point d'ancrage
stable pour les audits, la documentation et les imports publics.
-/
theorem fci_facade_loaded : True := trivial

end FCI