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
-- Dédié à Bernard Couret (1928–1999)
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
import CouretUnification.Core.SophieGermainHecke
import CouretUnification.Core.SophieGermainTowerLift
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
import CouretUnification.Core.Arithmetic

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
import CouretUnification.Core.LMFDBAlignment

import CouretUnification.Logic.H3.FiniteSpectralAPI
import CouretUnification.Logic.H3.ParityGamma30
import CouretUnification.Logic.H3.H3TestSpace
import CouretUnification.Logic.H3.RigidityParams
import CouretUnification.Logic.H3.C2Restricted
import CouretUnification.Logic.H3.C3Weak
import CouretUnification.Logic.H3.AlgebraTC

-- v35.3 — composition Phase B (recompose/spring-2026-pyramid-v0)
-- Éventail à 5 branches agrégeant les résultats substantiels de Logic.H3.
-- Tire transitivement les 14 modules Logic.H3 dans la fermeture.
-- RHClaimed = false. Sorry consommé : Lemma7Residual (branche β.2).
import CouretUnification.Logic.H3.PhaseBComposition

-- v35.4 — composition Phase B spécialisée Couret (spring-2026/couret-cabling)
-- Cinq branches (C-α, C-β, C-γ, C-δ, C-ε) câblant les pierres angulaires
-- arithmético-spectrales (Lambda, Parseval, ParsevalL5, T1_to_T7, FiniteCore)
-- à la chaîne H3.
-- RHClaimed = false. Aucun sorry consommé.
import CouretUnification.Logic.H3.PhaseBCompositionCouret

-- v35.4.1 — branche C-ζ pile B retenue (spring-2026/couret-cabling)
-- Cinq sous-branches Couret-ζ (ζ.1 à ζ.5) câblant les spectres harmoniques
-- explicites du triplet de Couret depuis la pile B retenue (TripletSpectrum,
-- TripletToFiniteSpectrum, TripletPowerSpectrum, TripletExceptionalPredicate,
-- CouretMinimalPackage). Tire transitivement les 16 fichiers de pile B retenue.
-- RHClaimed = false. Aucun sorry consommé.
import CouretUnification.Logic.H3.PhaseBCompositionCouretZeta

-- v35.4.2 — branche C-η combinatoire spectrale (spring-2026/couret-cabling)
-- Six sous-branches Couret-η (η.1 à η.6) câblant le noyau combinatoire
-- spectral fini T1-T7 : spectre certifié (CayleySpectrum), polynôme
-- caractéristique (CharPoly), unicité multiplicités (MultiplicityUniqueness),
-- déconnexion Cayley (CayleyConnected, ComponentSpectrum), classification
-- 63/255 (Classification63, Classification63Detail), récurrence des traces
-- (TraceRecurrence, FormuleLk). Tire transitivement les 13 fichiers
-- de la pile combinatoire (incluant Kurtosis, SpectralMoments, SpectralGap,
-- CenteredEigenspace par dépendance/cascade).
-- RHClaimed = false. Aucun sorry consommé.
import CouretUnification.Logic.H3.PhaseBCompositionCouretEta

-- v35.6
import CouretUnification.Core.SophieGermain

-- v35.7
import CouretUnification.Meta.Layer
import CouretUnification.Empirical.SophieGermainTransitions
import CouretUnification.Logic.C3Weak
import CouretUnification.Logic.CriticalLineTransferSpec
import CouretUnification.Logic.Doctrine
import CouretUnification.Logic.EulerBridgeInfinite
import CouretUnification.Logic.FEnriched30
import CouretUnification.Logic.FEnrichedSpec

import CouretUnification.Speculative.AnalogyMTF
import CouretUnification.Speculative.Ontology

-- v35.8
import CouretUnification.Empirical.SophieGermainExpected
import CouretUnification.Logic.EulerBridgeInfiniteCompat
import CouretUnification.Logic.EulerBridgeInfiniteReal
import CouretUnification.Logic.L10NoGoTheorem
import CouretUnification.Logic.OpenLocks

-- v35.8.1
import CouretUnification.Logic.L6Bridge

-- v35.8.1-bis
import CouretUnification.Meta.AuditHints

-- v35.8.5
import CouretUnification.Logic.H3.C3Weak_Gram
import CouretUnification.Logic.L6RatioEstimateDerived
import CouretUnification.Meta.Doctrine

-- v35.8.6
import CouretUnification.Analytic.GammaFactor
import CouretUnification.Logic.C3Weak_Gram  -- Facade vers H3.C3Weak_Gram
import CouretUnification.Logic.L6Analytic
import CouretUnification.Logic.L6Interface

-- v35.8.7
import CouretUnification.Logic.ChiralityFinite
import CouretUnification.Logic.ChiralityLinear

-- v35.8.8
import CouretUnification.AnalyticHorizon.Det2Transport
import CouretUnification.Logic.H3.CriticalLineTransferSpec
import CouretUnification.Logic.H3.LocalFactor
import CouretUnification.Logic.H3.MoebiusBridge
import CouretUnification.Logic.H3.SquarefreeDensity
import CouretUnification.Logic.H3.SquarefreeSupport
import CouretUnification.Logic.H3.LocalSquarefreeBridge
import CouretUnification.Logic.L6Analytic
import CouretUnification.Logic.L6Bridge
import CouretUnification.Logic.L6Interface
import CouretUnification.Logic.L6RatioEstimateDerived
import CouretUnification.Meta.Doctrine

-- v35.9-pre
import CouretUnification.AnalyticHorizon.Det2Obligations
import CouretUnification.AnalyticHorizon.Det2Transport
import CouretUnification.Logic.ExplicitFormula.ExplicitFormulaBridge
import CouretUnification.Logic.ExplicitFormula.TestFunctions
import CouretUnification.Logic.H3.HPCertificate
import CouretUnification.Meta.ProofJurisdiction

-- v35.9.0
import CouretUnification.Logic.ExplicitFormula.ArchimedeanSide
import CouretUnification.Logic.ExplicitFormula.ArithmeticWeight
import CouretUnification.Logic.ExplicitFormula.PrimeSide
import CouretUnification.Logic.ExplicitFormula.ZeroCounting

-- v35.9.1
import CouretUnification.Active
import CouretUnification.FCI.ModThirtyChecker -- TODO (TODO N1, I1)
import CouretUnification.Frozen
import CouretUnification.Logic.ExplicitFormula.TestPair
import CouretUnification.Logic.ExplicitFormula.TraceObject
import CouretUnification.Meta.SnapshotSentinel
-- TimeBridge LTB-0 (voir Frozen)
import CouretUnification.Logic.TimeBridge.Basic
import CouretUnification.Logic.TimeBridge.B2Calibration
import CouretUnification.Logic.TimeBridge.ModularFlowSpec

-- v35.9.2-prospective
import CouretUnification.Logic.TimeBridge.BostConnesMod30Spec

-- v36 Proof Jurisdiction
import CouretUnification.AnalyticHorizon.ArchimedeanDigammaCertificate
import CouretUnification.AnalyticHorizon.ZeroCountingCertificate
import CouretUnification.AnalyticHorizon.ExplicitFormulaBridgeAudit
import CouretUnification.AnalyticHorizon.Det2TransportCertificate
import CouretUnification.AnalyticHorizon.SoinInterface
import CouretUnification.AnalyticHorizon.ArchimedeanTorsionCertificate
import CouretUnification.AnalyticHorizon.TorsionZeroTransferCertificate
import CouretUnification.AnalyticHorizon.ActiveLayerFullAudit
import CouretUnification.AnalyticHorizon.A8ArchimedeanAbsorption
import CouretUnification.Logic.ExplicitFormula.ArchimedeanKernelBound
import CouretUnification.Logic.ExplicitFormula.ExplicitFormulaBridge
import CouretUnification.Logic.ExplicitFormula.PrimeSideCompactSupport
import CouretUnification.Logic.ExplicitFormula.StatusFlags
import CouretUnification.Logic.ExplicitFormula.TraceObject
import CouretUnification.Logic.ExplicitFormula.ZeroSideObligation
import CouretUnification.Release.ReleaseManifest

-- v36 Active-Extensions
import CouretUnification.Active.PrimeSideRealClosure
import CouretUnification.Active.TraceObjectEnriched

-- v37.0
import CouretUnification.EpistemicDiscipline.DoctrinalInvariants
import CouretUnification.Residue.ClosureTC
import CouretUnification.Residue.CycleCoset
import CouretUnification.Residue.TorsionLift210

-- v38.0
import CouretUnification.EpistemicDiscipline.BridgeStatus
import CouretUnification.Residue.PuncturedKlein30
import CouretUnification.AnalyticHorizon.TraceFormulaTargets
import CouretUnification.AnalyticHorizon.MomentRigidity30
import CouretUnification.AnalyticHorizon.ProtectedMinusTraceTargets
import CouretUnification.AnalyticHorizon.LegendreChannelCalibration
import CouretUnification.AnalyticHorizon.PerturbedSpectralIsolation
import CouretUnification.AnalyticHorizon.AdmissibleSigmaBand
import CouretUnification.AnalyticHorizon.PhaseStabilityTargets
import CouretUnification.AnalyticHorizon.DefectOperator30
import CouretUnification.Logic.Lock3.LocalDebiasing
import CouretUnification.Logic.Lock3.ProtectedTraceGate
import CouretUnification.Logic.Lock3.RHGuard
import CouretUnification.FCI.ModThirtyCheckerBridge     -- TODO (TODO G1 2 3)
import CouretUnification.FCI.CausalSupportImmunity      -- TODO (TODO-V1, S1, D1)
import CouretUnification.FCI.CausalSupportMeasureBridge -- TODO (TODO-M1 2 3 4)
import CouretUnification.FCI.FCI

-- v38.0.1
import CouretUnification.Logic.C2.Window
import CouretUnification.Logic.C2.Umbrella

-- v38.1
import CouretUnification.AnalyticHorizon.L6Stirling

-- v38.2 Sophie Germain (TowerLift)
import CouretUnification.Residue.SGShiftSqrt2
import CouretUnification.Residue.SGShiftSpectrum -- [O] frontière spectrale
import CouretUnification.Numerics.ScanSummary
import CouretUnification.Numerics.UseScanSummary
import CouretUnification.Experimental.TowerLift.ToyModelSpec
-- umbrella
import CouretUnification.SophieGermainUmbrella
import CouretUnification.Experimental.TowerLift

-- v38.3
import CouretUnification.Logic.H3.SpectralBridge

-- v38.4.3
import CouretUnification.Residue.Bridge.DefectOperatorBridge

-- v38.4.7 — fermeture coordonnée du sous-espace centré sur U30
import CouretUnification.Core.CenteredCoordinates

-- v38.5 ResGold
import CouretUnification.ResGold

-- v38.5.2 — ResGold QuadraticResonance — intégration A.4 (3/5 dominance) + A.4' (k_A4 = (1/2)·(·/5))
import CouretUnification.Core.QuadraticResonance

-- v38.5.3 — Sommes de caractères sur sous-groupe (ordre 2), moteur du défaut ponctuel — [D-formal]
import CouretUnification.Core.CharacterSubgroupSums
-- v38.5.3 — Loi d'annihilation globale sur un espace arbitraire
import CouretUnification.Core.PointDefectLemma
-- v38.5.3 — Classification spectrale finie des triplets de G₃₀
import CouretUnification.Core.G30Classification
-- v38.5.3 — Spécialisation à G₃₀ (|T|=3, fibres d'ordre 4 de taille 2).
import CouretUnification.Core.G30ClassificationFromPointDefect

-- v38.5.10+ — laboratoire compilable, sans sorry, pour fermeture C-04b SquarefreeDensity.
import CouretUnification.Logic.H3.SquarefreeDensityAsymptotic

-- TODO v38.1+ : une fois les TODO FCI levés, activer
-- globs := #[`CouretUnification.*] dans lakefile.lean pour forcer
-- la construction de tout fichier orphelin.
