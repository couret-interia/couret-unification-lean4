/-
# CouretUnification.All — agrégation exhaustive du dépôt

Ce fichier importe l’ensemble des modules du projet, y compris :
- couches canoniques,
- modules historiques,
- modules auxiliaires,
- interfaces, tables, façades, packages,
- composants expérimentaux ou de compatibilité.

Il sert d’agrégateur total pour audit, build exhaustif, inspection globale
et maintenance.

Pour l’entrée publique minimale et doctrinale, utiliser :
`import CouretUnification`
-/

-- ancien contenu massif de `CouretUnification.lean`

-- ══════════════════════════════════════════════════════════════
-- COURET-UNIFICATION — Démonstration unifiée la plus poussée
-- Programme Couret-Unification • Alexandre Couret • Avril 2026
-- Dédié à Bernard Couret (1928–2010)
-- RHClaimed = false
-- ══════════════════════════════════════════════════════════════

import CouretUnification.Core.Mod30
import CouretUnification.Core.FiniteOperator
import CouretUnification.Core.ExceptionalTriplets
import CouretUnification.Core.SpectralProfile
import CouretUnification.Core.Parseval
import CouretUnification.Core.Lambda
import CouretUnification.Core.SpectralGap
import CouretUnification.Core.CRTTransport
import CouretUnification.Core.InvariantE
import CouretUnification.Core.SophieGermainMod30
import CouretUnification.Core.HarmonicCertificate
import CouretUnification.Core.TripletDocumentaryCertificate
import CouretUnification.Core.CouretDocumentaryCertificate
import CouretUnification.Core.CouretPowerCertificate
import CouretUnification.Core.CouretMinimalPackage
import CouretUnification.Core.TripletCandidateInterface
import CouretUnification.Core.TripletQuadraticCandidateCertificate
import CouretUnification.Core.TripletQuadraticIntegralCandidateInterface
import CouretUnification.Core.TripletRawIntegralCriterion
import CouretUnification.Core.TripletRawQuadraticConsistency
import CouretUnification.Core.TripletLocalExceptionalCandidate
import CouretUnification.Core.TripletExceptionalPredicate

-- v32.1
import CouretUnification.Spectral.FiniteCore
import CouretUnification.Spectral.T2Gap

-- v32.4
import CouretUnification.Core.Classification63
import CouretUnification.Core.SpectralMoments

-- v32.5
import CouretUnification.Core.CayleySpectrum

-- v32.6
import CouretUnification.Core.CenteredEigenspace

-- v32.7
import CouretUnification.Core.Kurtosis

-- v32.8
import CouretUnification.Core.ParsevalL5

-- v32.9
import CouretUnification.Core.OddDimComplexObstruction

-- v32.10
import CouretUnification.Core.FormuleLk

-- v32.11
import CouretUnification.Core.TCAutoInverse

-- v32.12
import CouretUnification.Core.CayleyConnected

-- v32.13
import CouretUnification.Core.DefectProjection

-- v32.14
import CouretUnification.Core.ComponentSpectrum

-- v32.15
import CouretUnification.Core.Classification63Detail

-- v32.16
import CouretUnification.Core.CharPoly

-- v32.17
import CouretUnification.Core.MultiplicityUniqueness

-- v32.18
import CouretUnification.Core.TraceRecurrence

-- v32.19
import CouretUnification.Core.MersenneMod30

-- v32.20
import CouretUnification.Core.CarlemanUniqueness

-- v32.24
import CouretUnification.Core.SymplecticObstruction

-- v32.25
import CouretUnification.Analytic.AbelTailCompare
import CouretUnification.Analytic.AbelTailCore
import CouretUnification.Analytic.Integration
import CouretUnification.Analytic.VerifiedIntervals
import CouretUnification.Analytic.ZeroDensityAxioms
import CouretUnification.Core.FiniteCore
import CouretUnification.Core.SymplecticObstruction

import CouretUnification.FunctionalFoundation.DiscreteConnection
import CouretUnification.FunctionalFoundation.DiscretePaths

-- ─── COUCHE 1 : Noyau fini exact (0 sorry, 0 axiom) ────────
-- T1/T2 : G₃₀, TC, fantôme, CRT, Cayley, image quadratique
import CouretUnification.Core.U30
-- T3 : Spectre {3²,1⁴,(−1)²}, Fourier, Parseval, matrice
import CouretUnification.Finite.Foundations
import CouretUnification.Finite.Defect
-- T4-T7 : Projecteurs P₃/P₁/P₋, Pythagore, L_k, kurtosis
import CouretUnification.FiniteDefect.T1_to_T7

-- ─── COUCHE 4 : Pont H3 (1 sorry = lock3) ──────────────────
-- Structure du passage local → global
import CouretUnification.Logic.H3.FunctionalFoundation
import CouretUnification.Logic.H3.ArithmeticBridge
import CouretUnification.Logic.H3.AbelWeightedBound
import CouretUnification.Logic.H3.T5Weak
import CouretUnification.Logic.H3.Lemma7Residual
import CouretUnification.Logic.H3.Lock2Conditional
import CouretUnification.Logic.H3.ZeroMatching
import CouretUnification.Logic.H3.L10_MassPersistence
import CouretUnification.Logic.H3.L10Bridge
-- Distinction spectrale vs spatiale (M_RS = 0, B_21 ≠ 0)
import CouretUnification.Logic.H3.SpectralSpatial
-- Route C raffinée (Σ|E_d| ≤ θ · (φ/q) · S₁)
import CouretUnification.Logic.H3.RouteC
import CouretUnification.Logic.H3.Arithmetic

-- v32.44
import CouretUnification.Core.UnitsBridge
import CouretUnification.Core.CenteredSpace30
import CouretUnification.Core.Convolution30
import CouretUnification.Core.Characters30Bridge
import CouretUnification.Core.CayleyG30

-- v32.45 — pile B recâblée (vague 2B)
import CouretUnification.Core.TripletSpectrum
import CouretUnification.Core.TripletHarmonicSpectrum
import CouretUnification.Core.TripletToFiniteSpectrum
import CouretUnification.Core.TripletPowerSpectrum
import CouretUnification.Core.TripletExceptionalPredicate
import CouretUnification.Core.CouretDocumentaryCertificate
import CouretUnification.Core.CouretPowerCertificate
import CouretUnification.Core.CouretMinimalPackage

-- v35.1
import CouretUnification.Core.CharacterLemmas
import CouretUnification.Core.CharParity30
import CouretUnification.Core.CRTEquiv

import CouretUnification.Logic.H3.FiniteSpectralAPI
import CouretUnification.Logic.H3.ParityGamma30
import CouretUnification.Logic.H3.H3TestSpace
import CouretUnification.Logic.H3.RigidityParams
import CouretUnification.Logic.H3.C2Restricted
import CouretUnification.Logic.H3.C3Weak
import CouretUnification.Logic.H3.AlgebraTC

-- v35.4 — composition Phase B (recompose/spring-2026-pyramid-v0)
-- Éventail à 5 branches agrégeant les résultats substantiels de Logic.H3.
-- Tire transitivement les 14 modules Logic.H3 dans la fermeture.
-- RHClaimed = false. Sorry consommé : Lemma7Residual (branche β.2).
import CouretUnification.Logic.H3.PhaseBComposition
