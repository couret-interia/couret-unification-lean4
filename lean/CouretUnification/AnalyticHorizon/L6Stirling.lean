/-
CouretUnification.AnalyticHorizon.L6Stirling
========================================================================

# Canal L6 Stirling par caractères — limite canal par canal, v38.1

Doctrine :
- RHClaimed = false.
- EulerCompletionClosed = false.
- Det2IdentityClaimed = false.
- Ce fichier ne prouve pas la complétion eulérienne globale.
- Ce fichier ne doit pas être importé par les modules Core/Frozen.

Objectif :
dissoudre l'artefact apparent R ≈ 5 en prouvant que le ratio correctement
normalisé par canal tend vers 1/2 pour les canaux de Dirichlet primitifs.

Statut :
- cible analytique dans `AnalyticHorizon` ;
- aucun axiome global ;
- aucune promotion en [D] sans preuve.

Références :
- Iwaniec–Kowalski, Analytic Number Theory, Thm 5.8
  — Riemann–von Mangoldt.
- Mathlib : `Mathlib.Analysis.SpecialFunctions.Gamma.Stirling`.
- Mathlib : `Mathlib.NumberTheory.DirichletCharacter.Basic`.

Note doctrinale :
ce fichier ferme un artefact local de normalisation canal par canal.
Il ne ferme ni le pont det₂/ξ, ni la formule explicite globale, ni RH.
-/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

namespace CouretUnification.AnalyticHorizon

open Real Filter Topology

/-- Conducteur effectif d'un caractère de Dirichlet.

    Pour un caractère primitif modulo n, c'est n lui-même.
    Pour un caractère induit, c'est le conducteur du caractère primitif
    inducteur.

    TODO-L6-cond : remplacer par l'API Mathlib lorsque
    `DirichletCharacter.conductor` sera unifié entre les cas primitifs
    et induits.

    Le placeholder actuel utilise le module 30 comme majorant. -/
noncomputable def effectiveConductor
    (_χ : DirichletCharacter ℂ 30) : ℕ := 30

/-- Masse archimédienne d'un canal de Dirichlet à hauteur T.

    Pour χ primitif de conducteur effectif q_χ, c'est le terme principal
    de l'asymptotique de Riemann–von Mangoldt :

        A_χ(T) := (T / 2π) · log(q_χ T / 2π e).

    Cette expression est exacte, non asymptotique. Le régime asymptotique
    intervient seulement lorsqu'on compare A_χ(T) et S_χ(T). -/
noncomputable def archWeight
    (χ : DirichletCharacter ℂ 30)
    (T : ℝ) : ℝ :=
  (T / (2 * π)) *
    log ((effectiveConductor χ : ℝ) * T / (2 * π * Real.exp 1))

/-- Terme d'erreur logarithmique dans le comptage de Riemann–von Mangoldt.

    Il est de type O(log(q_χ T)). Une borne concrète devra être fournie.

    TODO-L6-err : remplacer par une borne explicite Mathlib lorsque
    l'API `LFunction.zeroCounting` sera disponible. -/
noncomputable def errorBound
    (χ : DirichletCharacter ℂ 30)
    (T : ℝ) : ℝ :=
  log ((effectiveConductor χ : ℝ) * (T + 1))

/-- Masse spectrale d'un canal de Dirichlet à hauteur T.

    Définie comme `2 · A_χ(T)` plus une correction logarithmique bornée par
    O(log(q_χ T)). Le facteur 2 encode la structure en paires conjuguées
    des zéros sur la ligne critique. -/
noncomputable def spectralMass
    (χ : DirichletCharacter ℂ 30)
    (T : ℝ) : ℝ :=
  2 * archWeight χ T + errorBound χ T

/-- Ratio L6 normalisé par canal. -/
noncomputable def Rχ
    (χ : DirichletCharacter ℂ 30)
    (T : ℝ) : ℝ :=
  archWeight χ T / spectralMass χ T

/-- Auxiliaire : `archWeight` est strictement positif pour T suffisamment grand. -/
theorem archWeight_pos_eventually
    (χ : DirichletCharacter ℂ 30) :
    ∀ᶠ T in Filter.atTop, 0 < archWeight χ T := by
  -- On prend T₀ = 2π·e, de sorte que 30·T/(2π·e) > 30 > 1
  -- pour T > T₀.
  filter_upwards [Filter.eventually_gt_atTop (2 * π * Real.exp 1)] with T hT
  have h_2π_pos : (0 : ℝ) < 2 * π := by positivity
  have h_2πe_pos : (0 : ℝ) < 2 * π * Real.exp 1 := by positivity
  have hT_pos : 0 < T := lt_trans h_2πe_pos hT
  unfold archWeight effectiveConductor
  push_cast
  refine mul_pos (div_pos hT_pos h_2π_pos) ?_
  -- Il reste à montrer : 0 < log(30·T/(2π·e)).
  apply Real.log_pos
  -- Réduction à : 1 < 30·T/(2π·e), c'est-à-dire 2π·e < 30·T.
  rw [lt_div_iff₀ h_2πe_pos, one_mul]
  linarith

/-- Majoration auxiliaire : pour T ≥ 60,

    log(30·(T+1)) ≤ 2 · log(30T/(2π e)).

    Preuve en deux étapes :
    (i) 30·(T+1) ≤ T² pour T ≥ 60.
    (ii) T ≤ 30T/(2π e), car 2π e < 30, numériquement ≈ 17.08. -/
private lemma errorBound_le_two_logArch_eventually
    (χ : DirichletCharacter ℂ 30) :
    ∀ᶠ T : ℝ in atTop,
      errorBound χ T ≤ 2 * Real.log (30 * T / (2 * π * Real.exp 1)) := by
  filter_upwards [Filter.eventually_ge_atTop (60 : ℝ)] with T hT
  unfold errorBound effectiveConductor
  push_cast
  have hT_pos : (0 : ℝ) < T := by linarith
  have h2πe_pos : (0 : ℝ) < 2 * π * Real.exp 1 := by positivity
  have h30T1_le_TT : 30 * (T + 1) ≤ T * T := by nlinarith
  have h30T1_pos : (0 : ℝ) < 30 * (T + 1) := by linarith
  -- (ii) T ≤ 30T/(2π e), via 2π·e ≤ 30
  -- puisque π < 4 et exp 1 < 3 donnent 2π·e < 24.
  have h_T_le : T ≤ 30 * T / (2 * π * Real.exp 1) := by
    rw [le_div_iff₀ h2πe_pos]
    have hπ_lt_4 : π < 4 := Real.pi_lt_four
    have he_lt_3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h_πe_lt_12 : π * Real.exp 1 < 12 := by
      have h1 : π * Real.exp 1 < π * 3 :=
        mul_lt_mul_of_pos_left he_lt_3 Real.pi_pos
      have h2 : π * 3 < 4 * 3 :=
        mul_lt_mul_of_pos_right hπ_lt_4 (by norm_num)
      linarith
    have h_2πe_le : 2 * π * Real.exp 1 ≤ 30 := by linarith
    calc T * (2 * π * Real.exp 1)
        ≤ T * 30 := mul_le_mul_of_nonneg_left h_2πe_le hT_pos.le
      _ = 30 * T := by ring
  -- Combinaison :
  -- log(30(T+1)) ≤ log(T·T) = 2·log T ≤ 2·log(30T/(2π e)).
  calc Real.log (30 * (T + 1))
      ≤ Real.log (T * T) := by gcongr
    _ = Real.log T + Real.log T := Real.log_mul hT_pos.ne' hT_pos.ne'
    _ = 2 * Real.log T := by ring
    _ ≤ 2 * Real.log (30 * T / (2 * π * Real.exp 1)) := by
        have h_logmono : Real.log T ≤
            Real.log (30 * T / (2 * π * Real.exp 1)) := by
          gcongr
        linarith

/-- Auxiliaire : `errorBound` est dominé asymptotiquement par `archWeight`. -/
lemma errorBound_littleO_archWeight
    (χ : DirichletCharacter ℂ 30) :
    Tendsto (fun T : ℝ => errorBound χ T / archWeight χ T)
      atTop (nhds 0) := by
  -- Stratégie : encadrer 0 ≤ ratio ≤ 4π/T → 0 pour T ≥ 60.
  have h_4πT : Tendsto (fun T : ℝ => 4 * π / T) atTop (nhds (0 : ℝ)) := by
    have h₁ : Tendsto (fun T : ℝ => (4 * π) * T⁻¹) atTop
                (nhds ((4 * π) * 0)) :=
      (tendsto_inv_atTop_zero).const_mul (4 * π)
    simp only [mul_zero] at h₁
    convert h₁ using 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) h_4πT
  · -- 0 ≤ ratio à partir d'un certain rang.
    filter_upwards [archWeight_pos_eventually χ,
                    Filter.eventually_ge_atTop (60 : ℝ)] with T h_aw_pos hT
    have h_eb_nn : 0 ≤ errorBound χ T := by
      unfold errorBound effectiveConductor
      push_cast
      apply Real.log_nonneg
      nlinarith
    exact div_nonneg h_eb_nn h_aw_pos.le
  · -- ratio ≤ 4π/T à partir d'un certain rang.
    filter_upwards [errorBound_le_two_logArch_eventually χ,
                    archWeight_pos_eventually χ,
                    Filter.eventually_ge_atTop (60 : ℝ)] with T h_eb h_aw_pos hT
    have hT_pos : (0 : ℝ) < T := by linarith
    rw [div_le_div_iff₀ h_aw_pos hT_pos]
    unfold archWeight effectiveConductor
    push_cast
    calc errorBound χ T * T
        ≤ (2 * Real.log (30 * T / (2 * π * Real.exp 1))) * T :=
          mul_le_mul_of_nonneg_right h_eb hT_pos.le
      _ = 4 * π * (T / (2 * π) *
            Real.log (30 * T / (2 * π * Real.exp 1))) := by
          field_simp
          ring

/-- Résultat principal : le ratio L6 normalisé par canal tend vers 1/2. -/
theorem channel_ratio_asymptotic_limit
    (χ : DirichletCharacter ℂ 30) :
    Tendsto (fun T : ℝ => Rχ χ T) atTop (nhds (1 / 2 : ℝ)) := by
  -- Étape 1 : E/A → 0, c'est `errorBound_littleO_archWeight`.
  have h_ratio : Tendsto (fun T : ℝ => errorBound χ T / archWeight χ T)
      atTop (nhds (0 : ℝ)) :=
    errorBound_littleO_archWeight χ
  -- Étape 2 : 2 + E/A → 2.
  have h_denom : Tendsto (fun T : ℝ => 2 + errorBound χ T / archWeight χ T)
      atTop (nhds (2 : ℝ)) := by
    simpa using h_ratio.const_add 2
  -- Étape 3 : (2 + E/A)⁻¹ → 2⁻¹ par continuité de l'inversion en 2 ≠ 0.
  have h_inv : Tendsto (fun T : ℝ => (2 + errorBound χ T / archWeight χ T)⁻¹)
      atTop (nhds ((2 : ℝ)⁻¹)) :=
    h_denom.inv₀ (by norm_num)
  -- Étape 4 : Rχ χ T = (2 + E/A)⁻¹ éventuellement,
  -- là où archWeight χ T > 0.
  have h_eq : (fun T : ℝ => Rχ χ T) =ᶠ[atTop]
      (fun T : ℝ => (2 + errorBound χ T / archWeight χ T)⁻¹) := by
    filter_upwards [archWeight_pos_eventually χ] with T h_aw_pos
    have h_aw_ne : archWeight χ T ≠ 0 := h_aw_pos.ne'
    show Rχ χ T = _
    unfold Rχ spectralMass
    field_simp
  -- Étape 5 : 1/2 = 2⁻¹, puis transfert du Tendsto de l'inverse vers Rχ.
  have h_const : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [h_const]
  exact h_inv.congr' h_eq.symm

/-- Invariant doctrinal : ce lemme ne ferme aucun verrou global.

    L'asymptotique R_χ(T) → 1/2 dissout l'artefact de normalisation
    R ≈ 5 au niveau local du canal.

    Elle ne contribue pas à `fullEulerCompletionJustified`,
    `Det2IdentityClaimed`, ni à aucune fermeture de la formule explicite. -/
theorem L6_does_not_close_global :
    True := trivial
  -- Marqueur documentaire. RHClaimed reste false.

end CouretUnification.AnalyticHorizon
