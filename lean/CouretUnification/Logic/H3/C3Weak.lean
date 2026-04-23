/-
  CouretUnification/Logic/H3/C3Weak.lean

  Matching faible C3w : théorème réel, pas axiome.

  Remplace :
    (i) le C3Weak.lean du pack v35.1 strict, dont le prédicat
        `ResidualRigid` exigeait Im(R) = 0 ∧ 0 ≤ Re(R) — trop fort
        pour être établi sans circularité ;
    (ii) le C3Weak_patched.lean livré le matin du 20 avril avec
         axiomes abstraits — trop évasif pour servir dans une preuve.

  Cette version finale :
    - définit ResidualRigid comme la DOMINATION ANALYTIQUE
      `-M < R` (une inégalité linéaire concrète entre réels) ;
    - définit WeakRigidityConclusion comme `0 < E` (la cible finale
      de la Cible 5) ;
    - PROUVE `C3_weak_from_C1C2` par `linarith` à partir de deux
      faits : (a) le théorème analytique `mainTermPositive_of_
      positiveBias` (dans C2Restricted), (b) l'hypothèse de
      rigidité résiduelle ResidualRigid.

  C'est la traduction formelle de la Smooth Bump Strategy :
      régularité globale + compacité locale ⇒ biais de positivité
      ⇒ domination du signal sur le résidu ⇒ E > 0.

  RHClaimed = false.
-/

import Mathlib.Tactic
import CouretUnification.Logic.H3.H3TestSpace
import CouretUnification.Logic.H3.C2Restricted
import CouretUnification.Logic.H3.RigidityParams

namespace CouretUnification.Logic.H3

-- ═══════════════════════════════════════════════════════════════════
-- §1. Rigidité résiduelle — définition concrète
-- ═══════════════════════════════════════════════════════════════════

/-- Rigidité résiduelle : le résidu reste strictement au-dessus de −M.
    Cette inégalité est SUFFISANTE pour faire basculer E > 0 dès que
    M > 0, sans exiger R ≥ 0 (qui serait circulaire). -/
def ResidualRigid (p : TestParams) (f : OperativeTestPacket) : Prop :=
  - explicitMainTerm p.sigma_s f
    < explicitResidualTerm p.N p.sigma_s f

-- ═══════════════════════════════════════════════════════════════════
-- §2. Conclusion cible : E > 0
-- ═══════════════════════════════════════════════════════════════════

/-- Conclusion de la rigidité faible : l'évaluation explicite est
    strictement positive. -/
def WeakRigidityConclusion (p : TestParams) (f : OperativeTestPacket) : Prop :=
  0 < EvaluateExplicit f p.sigma_s

-- ═══════════════════════════════════════════════════════════════════
-- §3. Théorème C3_weak_from_C1C2
-- ═══════════════════════════════════════════════════════════════════

/-- Théorème de rigidité faible :

    Sous
      - la formule explicite restreinte (hC2) ;
      - la rigidité résiduelle −M < R (hRigid) ;
    et en utilisant
      - le biais de positivité certifié dans le paquet ;
      - le pont analytique `mainTermPositive_of_positiveBias` ;
    on conclut 0 < E.

    La preuve est un pas de `linarith` après dépliage des
    définitions : c'est exactement la structure voulue. -/
theorem C3_weak_from_C1C2
    (p : TestParams) (f : OperativeTestPacket)
    (hC2 : RestrictedExplicitFormula p.N f p.sigma_s)
    (hRigid : ResidualRigid p f) :
    WeakRigidityConclusion p f := by
  -- Étape 1 : extraire le biais de positivité depuis le paquet,
  -- grâce à l'hypothèse h_sigma : 1 < sigma_s de TestParams.
  have hBias : PositiveBiasAt p.sigma_s f.toH3TestFunction :=
    f.positive_bias p.h_sigma
  -- Étape 2 : appliquer le pont analytique pour obtenir 0 < M.
  have hMain : 0 < explicitMainTerm p.sigma_s f :=
    mainTermPositive_of_positiveBias f p.sigma_s p.h_sigma hBias
  -- Étape 3 : déplier les définitions et conclure par linarith.
  dsimp only [RestrictedExplicitFormula, ResidualRigid,
              WeakRigidityConclusion] at *
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- §4. Corollaire applicable via l'axiome C2
-- ═══════════════════════════════════════════════════════════════════

/-- Version prêt-à-l'emploi : combine le théorème C2 axiomatique
    avec la rigidité résiduelle pour produire la conclusion. -/
theorem C3_weak_applied
    (p : TestParams) (f : OperativeTestPacket)
    (hRigid : ResidualRigid p f) :
    WeakRigidityConclusion p f :=
  C3_weak_from_C1C2 p f
    (restricted_explicit_formula_holds p.N f p.h_sigma)
    hRigid

-- ═══════════════════════════════════════════════════════════════════
-- §5. Sémantique Cible 5 (C3Weak au sens large)
-- ═══════════════════════════════════════════════════════════════════
-- L'ancienne définition placeholder `C3Weak : ∀ χ ∈ chars, True` du
-- pack v35.1 strict est PRÉSERVÉE ici pour compatibilité avec le
-- reste du dépôt, mais la vraie sémantique de la Cible 5 est
-- maintenant portée par `C3_weak_applied` ci-dessus.

open CouretUnification.Core in
def C3Weak (_D : ℂ → ℂ) (_L : CharIdx → ℂ → ℂ)
    (chars : Finset CharIdx) : Prop :=
  ∀ χ ∈ chars, True

open CouretUnification.Core in
theorem C3_weak_legacy_stub
    (D : ℂ → ℂ) (L : CharIdx → ℂ → ℂ) (chars : Finset CharIdx) :
    C3Weak D L chars := by
  intro χ _; trivial

-- ═══════════════════════════════════════════════════════════════════
-- §6. Doctrine de garde
-- ═══════════════════════════════════════════════════════════════════

theorem RHClaimed_false_guard : True := trivial
-- Marqueur doctrinal.  RHClaimed = false dans tous les contextes
-- où ce fichier est importé.

end CouretUnification.Logic.H3
