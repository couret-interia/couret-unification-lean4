/-
# CouretUnification/Active.lean

## Rôle

Umbrella "active" : importe les fichiers qui contiennent des sorries
documentés, correspondant aux fronts de recherche en cours.

Contrairement à Frozen.lean, ce fichier PEUT échouer au build si un
front casse temporairement. La CI doit traiter cet échec comme un
warning, pas un blocage.

## Statut (v38.5.1) — 18 sorries total

- Logic/C3Weak                        [1 sorry  — RIGIDITÉ FAIBLE DU RÉSIDU]
- Logic/EulerBridgeInfinite           [2 sorry  — COMPLÉTION EULÉRIENNE INFINIE]
- Logic/L6RatioEstimateDerived        [1 sorry  — ANALYTIC ASSEMBLY]
- Logic/L10NoGoTheorem                [2 sorry  — 1 CONCEPTUEL + 1 UPSTREAM]
- Logic/H3/RouteC                     [1 sorry  — LOCK 3 / EXISTENCE OPÉRATEUR]
- Logic/H3/Lemma7Residual             [1 sorry  — L7 / RÉSIDU SUR LIGNE CRITIQUE]
- Logic/H3/SquarefreeSupport          [1 sorry  — OBSOLETE, hors chemin]
- Logic/H3/SquarefreeDensity          [3 sorry  — ANALYTIC]
- Logic/H3/MoebiusBridge              [1 sorry  — SNAPSHOT API]
- AnalyticHorizon/Det2Transport       [1 sorry  — INSTANCIATION]
- Analytic/GammaFactor                [4 sorry  — PONT ARCHIMÉDIEN / GAMMA]

## Règle d'importation

Importe `Frozen` d'abord, puis étend avec les fronts actifs. Jamais
l'inverse.

## Commandes de test

```bash
# Sanity check rapide (~5 min)
lake build CouretUnification.Frozen

# Fronts actifs (peut échouer temporairement)
lake build CouretUnification.Active

# Tout (umbrella principale)
lake build CouretUnification
```

Layer : Meta (aggregator)
Sorry : 18
RHClaimed : false (hérité)
-/

-- Hérite de l'ensemble frozen
import CouretUnification.Frozen

-- Fronts actifs avec sorries documentés

-- L6 analytique
import CouretUnification.Logic.L6RatioEstimateDerived

-- No-go théorème L10
import CouretUnification.Logic.L10NoGoTheorem

-- Logic : fronts actifs
import CouretUnification.Logic.C3Weak -- [B] conditionnel formalisé (0 sorry - v38.5.6)

-- H3 : fronts actifs
import CouretUnification.Logic.H3.RouteC
import CouretUnification.Logic.H3.Lemma7Residual

-- AnalyticHorizon
import CouretUnification.AnalyticHorizon.Det2Transport

-- Analytic
import CouretUnification.Analytic.GammaFactor
