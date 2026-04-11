/-!
# CouretUnification — façade canonique

Entrée publique officielle du projet Couret–Unification.

Ce fichier expose la stratification doctrinale minimale du dépôt :

1. noyau fini exact ;
2. critère Couret-Défaut ;
3. absorption ;
4. pont H3 conditionnel ;
5. couronne doctrinale.

Pour l’agrégation exhaustive de tous les modules du dépôt,
voir `CouretUnification.All`.

## Garde épistémique
`RHClaimed = false`.
-/

-- ─── Couche 1 : noyau fini exact ────────────────────────────
import CouretUnification.Core.U30
import CouretUnification.Finite.Foundations
import CouretUnification.FiniteDefect.T1_to_T7

-- ─── Couche 2 : critère Couret-Défaut ───────────────────────
import CouretUnification.Criterion.CouretDefect

-- ─── Couche 3 : absorption ──────────────────────────────────
import CouretUnification.Absorption.AbsorptionMap

-- ─── Couche 4 : pont H3 conditionnel ────────────────────────
import CouretUnification.Logic.H3.FunctionalFoundation
import CouretUnification.Logic.H3.ArithmeticBridge
import CouretUnification.Logic.H3.Lemma7Residual
import CouretUnification.Logic.H3.Lock2Conditional
import CouretUnification.Logic.H3.ZeroMatching

-- ─── Couche 5 : couronne doctrinale ─────────────────────────
import CouretUnification.Crown.Crown