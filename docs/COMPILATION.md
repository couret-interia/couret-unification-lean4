# Notes de compilation

## Fichiers qui compilent déjà
- Core/FiniteCore.lean (native_decide)
- Core/SymplecticObstruction.lean (v32.24 validé)
- Logic/H3/* (chaîne conditionnelle, 1 sorry)
- Bridge/GlobalBridge.lean
- Crown.lean (si imports OK)

## AbelTailCore — 3 points à adapter pour Mathlib HEAD
1. **Imports** : `Asymptotics.Asymptotics` → `Asymptotics.Defs`,
   `Calculus.Deriv.Div` → `Calculus.Deriv.Inv`, ajouter `Topology.Basic`
2. **hasDerivAt_abelPrimitive** : `hasDerivAt_pow 2 t` retourne `↑2 * t^(2-1)`,
   adapter le `convert` ou utiliser `HasDerivAt.mul` + `HasDerivAt.inv`
3. **tendsto_log_div_sq_atTop** : `𝓝 0` → `nhds 0` ou `open Topology`

## Ordre de build recommandé
1. `lake clean && lake build CouretUnification.Core.FiniteCore`
2. `lake build CouretUnification.Core.SymplecticObstruction`
3. `lake build CouretUnification.Logic.H3.ZeroMatching`
4. `lake build CouretUnification.Bridge.GlobalBridge`
5. `lake build CouretUnification.Crown`
6. Fixer AbelTailCore (3 points ci-dessus)
7. `lake build CouretUnification.Analytic.Integration` (cascade)
8. `lake build` (tout)
