/-
Fichier racine actif du package CouretUnification v38.5.

Ce fichier importe le noyau fini consolidé ainsi que les fronts analytiques
actifs encore porteurs de `sorry` doctrinaux. Il n’est pas la façade Frozen.

Pour la façade strictement sans `sorry`, voir `CouretUnification.Frozen`.
Pour l’agrégateur exhaustif, voir `CouretUnification.All`.
-/

-- ─── Couche 1 : noyau fini exact (T1/T2) ───
-- T1/T2 : G₃₀, TC, fantôme, CRT, Cayley, image quadratique
import CouretUnification.Core.U30
-- T3 : Spectre {3²,1⁴,(−1)²}, Fourier, Parseval, matrice
import CouretUnification.Finite.Foundations
-- T4-T7 : Projecteurs P₃/P₁/P₋, Pythagore, L_k, kurtosis
import CouretUnification.FiniteDefect.T1_to_T7

-- pont H3 conditionnel via éventail Phase B
-- PhaseBComposition : éventail à 5 branches (α, β, γ, δ, η)
-- agrégeant les résultats substantiels de Logic.H3.
-- Tire transitivement 13 des 14 modules Logic.H3.
-- RHClaimed = false. Sorry consommé : Lemma7Residual (branche β.2).
import CouretUnification.Logic.H3.PhaseBComposition

-- Racines indépendantes non tirées par PhaseBComposition :
-- Route C raffinée (Σ|E_d| ≤ θ · (φ/q) · S₁)
import CouretUnification.Logic.H3.RouteC
-- Arithmétique fondamentale (μ, M(n), κ(q), squarefree)
import CouretUnification.Core.Arithmetic

-- Fondations épistémiques
import CouretUnification.Meta.Doctrine

-- Couche Logic — briques fermées
import CouretUnification.Logic.EulerBridgeInfiniteCompat
import CouretUnification.Logic.C3Weak_Gram

-- ─── Couche 2 : opérateur centré + chiralité ───
-- Couche Logic / Gold — chiralité finie mod 30 (since v35.8.7)
import CouretUnification.Logic.ChiralityFinite

-- Couche Logic / Diamond — réalisation matricielle Ω₇ (since v35.8.7)
import CouretUnification.Logic.ChiralityLinear

-- ─── Couche 3 : fronts analytiques actifs ───
-- Sorry consommés 4
import CouretUnification.Analytic.GammaFactor

-- Sorry consommé 1
import CouretUnification.Logic.C3Weak

-- Sorry consommés 2
import CouretUnification.Logic.EulerBridgeInfinite

-- Couche Logic — interface L6 (since v35.8.6)
import CouretUnification.Logic.L6Interface

-- Couche Logic — interface L6
import CouretUnification.Logic.L6Bridge

-- Couche Logic — livrable principal v35.8.6
import CouretUnification.Logic.L6Analytic

-- Couche Logic — Step C branché sur L6Analytic
import CouretUnification.Logic.L6RatioEstimateDerived

-- Couche Logic — obstruction topologique (Sorry consommés 2)
import CouretUnification.Logic.L10NoGoTheorem

-- Couche Logic — registre doctrinal (invariant RH-wall)
import CouretUnification.Logic.OpenLocks

-- Couche Logic / H3 — front arithmétique-analytique (since v35.8.8)
import CouretUnification.Logic.H3.LocalFactor
-- Sorry consommé 1
import CouretUnification.Logic.H3.SquarefreeSupport
-- Sorry consommés 3
import CouretUnification.Logic.H3.SquarefreeDensity
-- Sorry consommé 1
import CouretUnification.Logic.H3.MoebiusBridge
import CouretUnification.Logic.H3.CriticalLineTransferSpec

-- Couche AnalyticHorizon — transport analytique régularisé (since v35.8.8)
-- Sorry consommé 1
import CouretUnification.AnalyticHorizon.Det2Transport
