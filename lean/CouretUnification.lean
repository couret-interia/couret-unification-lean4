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
-- T1/T2 : G₃₀, TC, fantôme, CRT, Cayley, image quadratique
import CouretUnification.Core.U30
-- T3 : Spectre {3²,1⁴,(−1)²}, Fourier, Parseval, matrice
import CouretUnification.Finite.Foundations
-- T4-T7 : Projecteurs P₃/P₁/P₋, Pythagore, L_k, kurtosis
import CouretUnification.FiniteDefect.T1_to_T7

-- ─── Couche 2 : critère Couret-Défaut ───────────────────────
-- Fonctionnelle I(φ), classe admissible, direction HRG
import CouretUnification.Criterion.CouretDefect

-- ─── Couche 3 : absorption ──────────────────────────────────
-- Carte ℜ(L,T), Ω_good, lemme hybride, résonances
import CouretUnification.Absorption.AbsorptionMap

-- ─── Couche 4 : pont H3 conditionnel ────────────────────────
-- Structure du passage local → global
import CouretUnification.Bridge.GlobalBridge
import CouretUnification.Logic.H3.FunctionalFoundation
import CouretUnification.Logic.H3.ArithmeticBridge
-- Lemme Abel pondéré (annulation par caractère non trivial)
import CouretUnification.Logic.H3.AbelWeightedBound
-- T5_weak + T9 (localisation de Schur)
import CouretUnification.Logic.H3.T5Weak
import CouretUnification.Logic.H3.Lemma7Residual
import CouretUnification.Logic.H3.Lock2Conditional
import CouretUnification.Logic.H3.ZeroMatching
-- L10 : persistance de masse sectorielle (fermable par BDH)
import CouretUnification.Logic.H3.L10_MassPersistence
import CouretUnification.Logic.H3.L10Bridge
-- Distinction spectrale vs spatiale (M_RS = 0, B_21 ≠ 0)
import CouretUnification.Logic.H3.SpectralSpatial
-- Route C raffinée (Σ|E_d| ≤ θ · (φ/q) · S₁)
import CouretUnification.Logic.H3.RouteC
import CouretUnification.Logic.H3.Arithmetic

-- ─── Couche 5 : couronne doctrinale ─────────────────────────
-- Chaîne complète : H1→H3.A→Hadamard→Lock2→Lock3→RH
import CouretUnification.Crown.Crown

-- ─── Couche 6 : absorption avancée / verrou L6 ──────────────
-- L6 : absorption archimédienne par canal (quasi-fermé)
import CouretUnification.Criterion.L6_Absorption

-- ─── route D : Contradiction formelle avec kappa ────────────
import CouretUnification.Criterion.RouteDContradiction

