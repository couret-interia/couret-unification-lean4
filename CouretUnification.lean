/-
# CouretUnification.lean (fichier racine)

Fichier racine du package `CouretUnification` v35.8.6.
Importe tous les modules du projet dans l'ordre doctrinal.

## Ordre d'importation
  1. Meta       (fondations non-mathématiques)
  2. Logic.*    (couche de travail actuelle)

## Invariant global
`RHClaimed = false` est vérifié à la compilation via
`Logic.OpenLocks.no_rh_wall_lock_proved`.
-/

-- Fondations épistémiques
import CouretUnification.Meta.Doctrine

-- Couche Logic — briques fermées
import CouretUnification.Logic.EulerBridgeInfiniteCompat
import CouretUnification.Logic.C3Weak_Gram

-- Couche Logic / Gold — chiralité finie mod 30 (NOUVEAU v35.8.7)
import CouretUnification.Logic.ChiralityFinite

-- Couche Logic / Diamond — réalisation matricielle Ω₇ (NOUVEAU v35.8.7)
import CouretUnification.Logic.ChiralityLinear

-- Couche Logic — interface L6 (NOUVEAU v35.8.6)
import CouretUnification.Logic.L6Interface

-- Couche Logic — interface L6
import CouretUnification.Logic.L6Bridge

-- Couche Logic — livrable principal v35.8.6
import CouretUnification.Logic.L6Analytic

-- Couche Logic — Step C branché sur L6Analytic
import CouretUnification.Logic.L6RatioEstimateDerived

-- Couche Logic — obstruction topologique
import CouretUnification.Logic.L10NoGoTheorem

-- Couche Logic — registre doctrinal (invariant RH-wall)
import CouretUnification.Logic.OpenLocks

-- Couche Logic / H3 — front arithmétique-analytique (NOUVEAU v35.8.8)
import CouretUnification.Logic.H3.LocalFactor
import CouretUnification.Logic.H3.SquarefreeSupport
import CouretUnification.Logic.H3.SquarefreeDensity
import CouretUnification.Logic.H3.MoebiusBridge
import CouretUnification.Logic.H3.CriticalLineTransferSpec

-- Couche AnalyticHorizon — transport analytique régularisé (NOUVEAU v35.8.8)
import CouretUnification.AnalyticHorizon.Det2Transport
