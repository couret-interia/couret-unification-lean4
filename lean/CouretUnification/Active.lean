/-
# CouretUnification/Active.lean

## Rôle

Umbrella "active" : importe les fichiers qui contiennent des sorries
documentés, correspondant aux fronts de recherche en cours.

Contrairement à Frozen.lean, ce fichier PEUT échouer au build si un
front casse temporairement. La CI doit traiter cet échec comme un
warning, pas un blocage.

## Statut (v35.8.8) — 9 sorries total

- Logic/L6Analytic                    [1 sorry  — ANALYTIC/Stirling]
- Logic/L6RatioEstimateDerived        [1 sorry  — ANALYTIC ASSEMBLY]
- Logic/L10NoGoTheorem                [3 sorry  — 1 CONCEPTUEL + 2 UPSTREAM]
- Logic/H3/SquarefreeSupport          [1 sorry  — OBSOLETE, hors chemin]
- Logic/H3/SquarefreeDensity          [3 sorry  — ANALYTIC]
- Logic/H3/MoebiusBridge              [1 sorry  — SNAPSHOT API]
- AnalyticHorizon/Det2Transport       [1 sorry  — DOCTRINAL unique]

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
Sorry : 11 (cf. BUILD.md pour inventaire détaillé)
RHClaimed : false (hérité)
-/

-- Hérite de l'ensemble frozen
import CouretUnification.Frozen

-- Fronts actifs avec sorries documentés

-- L6 analytique
import CouretUnification.Logic.L6Analytic
import CouretUnification.Logic.L6RatioEstimateDerived

-- No-go théorème L10
import CouretUnification.Logic.L10NoGoTheorem

-- H3 : fronts actifs
import CouretUnification.Logic.H3.SquarefreeSupport
import CouretUnification.Logic.H3.SquarefreeDensity
import CouretUnification.Logic.H3.MoebiusBridge

-- AnalyticHorizon
import CouretUnification.AnalyticHorizon.Det2Transport
