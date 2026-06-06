import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped BigOperators
open Finset

noncomputable section

namespace CouretUnification.Logic.H3.L10Bridge

variable {X : Type*} [Fintype X]

-- ═══════════════════════════════════════════════════════════
-- §1. Définitions fondamentales
-- ═══════════════════════════════════════════════════════════

/-- Produit scalaire `L²` normalisé sur un type fini `X`. -/
def l2Inner (f g : X → ℂ) : ℂ :=
  ((Fintype.card X : ℂ)⁻¹) * ∑ x : X, f x * (starRingEnd ℂ) (g x)

/-- Norme `L²` au carré, définie comme la partie réelle de `l2Inner f f`. -/
def l2NormSq (f : X → ℂ) : ℝ :=
  (l2Inner f f).re

/-- Norme `L²` associée à `l2NormSq`. -/
def l2Norm (f : X → ℂ) : ℝ :=
  Real.sqrt (l2NormSq f)

-- ═══════════════════════════════════════════════════════════
-- §2. Propriétés de l2Inner
-- ═══════════════════════════════════════════════════════════

/-- Linéarité de `l2Inner` en son premier argument. -/
lemma l2Inner_add_left (f g h : X → ℂ) :
    l2Inner (f + g) h = l2Inner f h + l2Inner g h := by
  unfold l2Inner
  simp [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

/-- Additivité de `l2Inner` en son second argument. -/
lemma l2Inner_add_right (f g h : X → ℂ) :
    l2Inner f (g + h) = l2Inner f g + l2Inner f h := by
  unfold l2Inner
  simp [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/-- Compatibilité de `l2Inner` avec la multiplication scalaire à gauche. -/
lemma l2Inner_smul_left (c : ℂ) (f g : X → ℂ) :
    l2Inner (c • f) g = c * l2Inner f g := by
  unfold l2Inner
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    ((Fintype.card X : ℂ)⁻¹) * ∑ x : X, c * f x * (starRingEnd ℂ) (g x)
        =
      ((Fintype.card X : ℂ)⁻¹) * ∑ x : X, c * (f x * (starRingEnd ℂ) (g x)) := by
          congr 1; apply Finset.sum_congr rfl; intro x _; ring
    _ =
      ((Fintype.card X : ℂ)⁻¹) * (c * ∑ x : X, f x * (starRingEnd ℂ) (g x)) := by
          congr 1; rw [Finset.mul_sum]
    _ = c * (((Fintype.card X : ℂ)⁻¹) * ∑ x : X, f x * (starRingEnd ℂ) (g x)) := by
          ring

/-- Compatibilité de `l2Inner` avec la multiplication scalaire à droite,
avec conjugaison du scalaire. -/
lemma l2Inner_smul_right (c : ℂ) (f g : X → ℂ) :
    l2Inner f (c • g) = (star c) * l2Inner f g := by
  unfold l2Inner
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  calc
    ((Fintype.card X : ℂ)⁻¹) *
        ∑ x : X, f x * ((starRingEnd ℂ) c * (starRingEnd ℂ) (g x))
      =
    ((Fintype.card X : ℂ)⁻¹) *
        ∑ x : X, (star c) * (f x * (starRingEnd ℂ) (g x)) := by
          congr 1; apply Finset.sum_congr rfl; intro x _; simp [mul_left_comm]
    _ =
    ((Fintype.card X : ℂ)⁻¹) *
        ((star c) * ∑ x : X, f x * (starRingEnd ℂ) (g x)) := by
          congr 1; rw [Finset.mul_sum]
    _ = (star c) *
        (((Fintype.card X : ℂ)⁻¹) * ∑ x : X, f x * (starRingEnd ℂ) (g x)) := by
          ring

/-- Scission de `l2Inner` selon une décomposition `main = diag + off`. -/
lemma l2Inner_split (main diag off Psi : X → ℂ)
    (hsplit : ∀ x, main x = diag x + off x) :
    l2Inner main Psi = l2Inner diag Psi + l2Inner off Psi := by
  have hmain : main = diag + off := funext hsplit
  rw [hmain, l2Inner_add_left]

-- ═══════════════════════════════════════════════════════════
-- §2b. Symétrie hermitienne
-- ═══════════════════════════════════════════════════════════

/-- Symétrie hermitienne : l2Inner g f = star (l2Inner f g). -/
lemma l2Inner_conj_symm (f g : X → ℂ) :
    l2Inner g f = star (l2Inner f g) := by
  unfold l2Inner
  simp [mul_comm]

-- ═══════════════════════════════════════════════════════════
-- §2c. Mise à l’échelle + non-négativité
-- ═══════════════════════════════════════════════════════════

/-- Comportement de `l2NormSq` sous multiplication par le scalaire réel `ρ^d`. -/
lemma l2NormSq_smul_real_pow (ρ : ℝ) (d : ℕ) (f : X → ℂ) :
    l2NormSq (((ρ : ℂ) ^ d) • f) = (ρ ^ (2 * d)) * l2NormSq f := by
  unfold l2NormSq
  rw [l2Inner_smul_left, l2Inner_smul_right]
  have hconj : star ((ρ : ℂ) ^ d) = (ρ : ℂ) ^ d := by
    simp [Complex.conj_ofReal]
  rw [hconj, ← mul_assoc, ← pow_add]
  have hdd : d + d = 2 * d := by ring
  rw [hdd]
  have hcast : (↑ρ : ℂ) ^ (2 * d) = ↑(ρ ^ (2 * d)) := by push_cast; ring
  rw [hcast]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Non-négativité de la norme `L²` au carré. -/
lemma l2NormSq_nonneg (f : X → ℂ) : 0 ≤ l2NormSq f := by
  unfold l2NormSq l2Inner
  have hsum :
      (∑ x : X, f x * (starRingEnd ℂ) (f x))
        = ∑ x : X, (Complex.normSq (f x) : ℂ) := by
    apply Finset.sum_congr rfl
    intro x _
    simp [Complex.mul_conj]
  have hcard :
      ((Fintype.card X : ℂ)⁻¹) = ↑((Fintype.card X : ℝ)⁻¹) := by
    simp
  rw [hcard, hsum]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  simp only [zero_mul, sub_zero, Complex.re_sum, Complex.ofReal_re]
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg (fun x _ => Complex.normSq_nonneg (f x))

variable [DecidableEq X]

-- ═══════════════════════════════════════════════════════════
-- §3. Structure de décomposition par couches
-- ═══════════════════════════════════════════════════════════

/-- Structure abstraite de décomposition orthogonale par couches finies. -/
structure LayerDecomposition (X : Type*) [Fintype X] [DecidableEq X] where
  /-- Projection de `f` sur la couche `d`. -/
  layer : ℕ → (X → ℂ) → (X → ℂ)
  /-- Support fini des couches non nulles de `f`. -/
  support : (X → ℂ) → Finset ℕ
  /-- Hors du support, la couche est nulle. -/
  support_spec : ∀ f d, d ∉ support f → layer d f = 0
  /-- Reconstruction de `f` comme somme de ses couches. -/
  reconstruction : ∀ f, f = ∑ d ∈ support f, layer d f
  /-- Orthogonalité des couches distinctes. -/
  orthogonal : ∀ f {d e : ℕ}, d ≠ e →
    l2Inner (layer d f) (layer e f) = 0
  /-- Théorème de Pythagore abstrait pour une famille orthogonale finie. -/
  pythagorean_general : ∀ (S : Finset ℕ) (g : ℕ → (X → ℂ)),
    (∀ d ∈ S, ∀ e ∈ S, d ≠ e → l2Inner (g d) (g e) = 0) →
    l2NormSq (∑ d ∈ S, g d) = ∑ d ∈ S, l2NormSq (g d)

variable (LD : LayerDecomposition X)

/-- Projection basse : somme des couches de degré `d ≤ d0`. -/
def lowProj (d0 : ℕ) (f : X → ℂ) : X → ℂ :=
  ∑ d ∈ (LD.support f).filter fun d => d ≤ d0, LD.layer d f

/-- Opérateur de bruit : chaque couche `d` est pondérée par `ρ^d`. -/
def noiseOp (ρ : ℝ) (f : X → ℂ) : X → ℂ :=
  ∑ d ∈ LD.support f, ((ρ : ℂ) ^ d) • LD.layer d f

-- ═══════════════════════════════════════════════════════════
-- §4. Structures pour le bridge
-- ═══════════════════════════════════════════════════════════

/-- Décomposition d’un terme principal en partie diagonale et hors-diagonale. -/
structure DiagOffSplit (main diag off : X → ℂ) where
  /-- Égalité ponctuelle `main = diag + off`. -/
  sum_eq : ∀ x, main x = diag x + off x

/-- Données quantitatives du certificat de bridge. -/
structure CertificateData where
  /-- Partie diagonale. -/
  diag : X → ℂ
  /-- Partie hors-diagonale. -/
  off  : X → ℂ
  /-- Fonction test. -/
  Psi  : X → ℂ
  /-- Borne de norme pour `Psi`. -/
  B : ℝ
  /-- Taille minimale du couplage diagonal. -/
  beta : ℝ
  /-- Paramètre de contrôle du terme hors-diagonal. -/
  lambda : ℝ
  /-- Positivité de `B`. -/
  hB_pos : 0 < B
  /-- Positivité de `beta`. -/
  hbeta_pos : 0 < beta
  /-- Non-négativité de `lambda`. -/
  hlambda_nonneg : 0 ≤ lambda
  /-- Borne `l2Norm Psi ≤ B`. -/
  hnorm : l2Norm Psi ≤ B
  /-- Borne inférieure diagonale. -/
  hbeta_bound : beta ≤ ‖l2Inner diag Psi‖
  /-- Borne supérieure hors-diagonale. -/
  hgamma_bound : ‖l2Inner off Psi‖ ≤ lambda * beta
  /-- Condition stricte `lambda < 1`. -/
  hlambda_lt_one : lambda < 1

/-- Données de régularité/filtrage pour le cadre HC. -/
structure HCData where
  /-- Exposant `p`. -/
  p : ℝ
  /-- Paramètre `rho`. -/
  rho : ℝ
  /-- Borne inférieure `1 < p`. -/
  hp_lower : 1 < p
  /-- Borne supérieure `p ≤ 2`. -/
  hp_upper : p ≤ 2
  /-- Positivité de `rho`. -/
  hrho_pos : 0 < rho
  /-- Borne supérieure `rho ≤ 1`. -/
  hrho_upper : rho ≤ 1

-- ═══════════════════════════════════════════════════════════
-- §5. Théorèmes délégués
-- ═══════════════════════════════════════════════════════════

/-- Orthogonalité des couches distinctes, déléguée à `LD`. -/
theorem layer_orthogonal (f : X → ℂ) {d e : ℕ} (hde : d ≠ e) :
    l2Inner (LD.layer d f) (LD.layer e f) = 0 :=
  LD.orthogonal f hde

/-- Une couche hors du support est nulle, délégué à `LD`. -/
theorem layer_eq_zero_of_not_mem_support (f : X → ℂ) (d : ℕ)
    (hd : d ∉ LD.support f) :
    LD.layer d f = 0 :=
  LD.support_spec f d hd

/-- Reconstruction de `f` comme somme de ses couches, déléguée à `LD`. -/
theorem sum_layers_eq (f : X → ℂ) :
    f = ∑ d ∈ LD.support f, LD.layer d f :=
  LD.reconstruction f

-- ═══════════════════════════════════════════════════════════
-- §6. FERMÉ : Pythagore pour noiseOp et lowProj
-- ═══════════════════════════════════════════════════════════

/-- Les couches pondérées de `noiseOp` restent orthogonales. -/
lemma noise_layers_orthogonal (ρ : ℝ) (f : X → ℂ) (d e : ℕ)
    (hde : d ≠ e) :
    l2Inner (((ρ : ℂ) ^ d) • LD.layer d f)
            (((ρ : ℂ) ^ e) • LD.layer e f) = 0 := by
  rw [l2Inner_smul_left, l2Inner_smul_right]
  rw [LD.orthogonal f hde]
  simp

/-- Formule de Pythagore pour la norme au carré de `noiseOp`. -/
theorem l2NormSq_noiseOp (ρ : ℝ) (f : X → ℂ) :
    l2NormSq (noiseOp LD ρ f)
      = ∑ d ∈ LD.support f, (ρ ^ (2 * d)) * l2NormSq (LD.layer d f) := by
  unfold noiseOp
  rw [LD.pythagorean_general (LD.support f) (fun d => ((ρ : ℂ) ^ d) • LD.layer d f)
      (fun d hd e he hde => noise_layers_orthogonal LD ρ f d e hde)]
  congr 1
  ext d
  exact l2NormSq_smul_real_pow ρ d (LD.layer d f)

/-- Formule de Pythagore pour la norme au carré de `lowProj`. -/
theorem l2NormSq_lowProj (d0 : ℕ) (f : X → ℂ) :
    l2NormSq (lowProj LD d0 f)
      = ∑ d ∈ (LD.support f).filter fun d => d ≤ d0,
          l2NormSq (LD.layer d f) := by
  unfold lowProj
  exact LD.pythagorean_general _ (fun d => LD.layer d f)
    (fun d hd e he hde => LD.orthogonal f hde)

-- ═══════════════════════════════════════════════════════════
-- §7. Cauchy-Schwarz — FERMÉ
-- ═══════════════════════════════════════════════════════════

omit [DecidableEq X] in
/-- Identifie le produit scalaire normalisé compact `l2Inner`
au produit scalaire pondéré `wInner` utilisant `cWeight`,
avec arguments inversés pour respecter la convention de conjugaison. -/
lemma l2Inner_eq_wInner_cWeight_flip (f g : X → ℂ) :
    l2Inner f g = RCLike.wInner (𝕜 := ℂ) RCLike.cWeight g f := by
  unfold l2Inner
  rw [RCLike.wInner_cWeight_eq_smul_wInner_one, RCLike.wInner_one_eq_sum]
  have hsum :
      (∑ i : X, f i * (starRingEnd ℂ) (g i))
        =
      (∑ i : X, inner ℂ (g i) (f i)) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [RCLike.inner_apply]
  rw [hsum]
  simp [NNRat.smul_def]

omit [DecidableEq X] in
/-- Exprime `l2NormSq` comme norme au carré normalisée
de `WithLp.toLp 2 f`. -/
lemma l2NormSq_eq_scaled_norm_sq (f : X → ℂ) :
    l2NormSq f = ((Fintype.card X : ℝ)⁻¹) * ‖WithLp.toLp 2 f‖ ^ 2 := by
  unfold l2NormSq
  rw [l2Inner_eq_wInner_cWeight_flip]
  rw [RCLike.wInner_cWeight_eq_smul_wInner_one, RCLike.wInner_one_eq_inner]
  rw [inner_self_eq_norm_sq_to_K]
  simp [NNRat.smul_def, Complex.mul_re, pow_two]

omit [DecidableEq X] in
/-- Forme fermée de `l2Norm` en fonction de la norme finie `L2` standard. -/
lemma l2Norm_eq_scaled_norm (f : X → ℂ) :
    l2Norm f = Real.sqrt ((Fintype.card X : ℝ)⁻¹) * ‖WithLp.toLp 2 f‖ := by
  unfold l2Norm
  rw [l2NormSq_eq_scaled_norm_sq]
  have h1 : 0 ≤ ((Fintype.card X : ℝ)⁻¹) := by
    positivity
  have h2 : 0 ≤ ‖WithLp.toLp 2 f‖ := norm_nonneg _
  rw [pow_two, Real.sqrt_mul h1]
  congr 1
  have hs : ‖WithLp.toLp 2 f‖ * ‖WithLp.toLp 2 f‖ = ‖WithLp.toLp 2 f‖ ^ 2 := by
    ring
  rw [hs, Real.sqrt_sq_eq_abs, abs_of_nonneg h2]

omit [DecidableEq X] in
/-- Inégalité de Cauchy-Schwarz en dimension finie pour `l2Inner`,
réduite au produit scalaire standard `WithLp`. -/
lemma cauchy_schwarz_l2 (f g : X → ℂ) :
    ‖l2Inner f g‖ ≤ l2Norm f * l2Norm g := by
  rw [l2Inner_eq_wInner_cWeight_flip]
  rw [RCLike.wInner_cWeight_eq_smul_wInner_one, RCLike.wInner_one_eq_inner]
  rw [l2Norm_eq_scaled_norm, l2Norm_eq_scaled_norm]
  set c : ℝ := (Fintype.card X : ℝ)⁻¹
  set a : ℂ := ((c : ℝ) : ℂ)
  set uf : ℝ := ‖WithLp.toLp 2 f‖
  set ug : ℝ := ‖WithLp.toLp 2 g‖
  set z : ℂ := inner ℂ (WithLp.toLp 2 g) (WithLp.toLp 2 f)

  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity

  have hsmul : (((Fintype.card X : ℚ≥0)⁻¹) • z) = a * z := by
    dsimp [a, c]
    rw [NNRat.smul_def]
    simp

  have hcoeff : norm a = c := by
    dsimp [a]
    rw [Complex.norm_real, Real.norm_of_nonneg hc_nonneg]

  have hleft : norm (((Fintype.card X : ℚ≥0)⁻¹) • z) = c * norm z := by
    rw [hsmul, norm_mul, hcoeff]

  have hsq : (Real.sqrt c) ^ 2 = c := by
    exact Real.sq_sqrt hc_nonneg

  have hfinal : c * (uf * ug) = (Real.sqrt c * uf) * (Real.sqrt c * ug) := by
    calc
      c * (uf * ug) = (Real.sqrt c) ^ 2 * (uf * ug) := by rw [hsq]
      _ = (Real.sqrt c * uf) * (Real.sqrt c * ug) := by ring

  calc
    norm (((Fintype.card X : ℚ≥0)⁻¹) • inner ℂ (WithLp.toLp 2 g) (WithLp.toLp 2 f))
        = norm (((Fintype.card X : ℚ≥0)⁻¹) • z) := by
            simp [z]
    _ = c * norm z := hleft
    _ ≤ c * (ug * uf) := by
        dsimp [z, ug, uf]
        gcongr
        exact norm_inner_le_norm _ _
    _ = c * (uf * ug) := by ring
    _ = (Real.sqrt c * uf) * (Real.sqrt c * ug) := hfinal

-- ═══════════════════════════════════════════════════════════
-- §8. Bridge — FERMÉ (modulo CS)
-- ═══════════════════════════════════════════════════════════

omit [DecidableEq X] in
/-- Théorème de bridge. FERMÉ.
    Utilise : `l2Inner_split`, triangle inversé (`norm_add_le` + `norm_neg`),
    Cauchy-Schwarz, `sq_le_sq'`, `Real.sq_sqrt`, `l2NormSq_nonneg`. -/
theorem bridge_lower_bound
    (main : X → ℂ)
    (CD : CertificateData (X := X))
    (hsplit : ∀ x, main x = CD.diag x + CD.off x) :
    ((1 - CD.lambda) ^ 2 * CD.beta ^ 2) / (CD.B ^ 2)
      ≤ l2NormSq main := by
  set a := l2Inner CD.diag CD.Psi
  set b := l2Inner CD.off CD.Psi
  have hab : l2Inner main CD.Psi = a + b :=
    l2Inner_split main CD.diag CD.off CD.Psi hsplit
  have hrev : ‖a‖ - ‖b‖ ≤ ‖a + b‖ := by
    have h1 : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
      calc ‖a‖ = ‖(a + b) + (-b)‖ := by congr 1; ring
        _ ≤ ‖a + b‖ + ‖-b‖ := norm_add_le _ _
        _ = ‖a + b‖ + ‖b‖ := by rw [norm_neg]
    linarith
  have htri : (1 - CD.lambda) * CD.beta ≤ ‖l2Inner main CD.Psi‖ := by
    rw [hab]
    calc (1 - CD.lambda) * CD.beta
        = CD.beta - CD.lambda * CD.beta := by ring
      _ ≤ ‖a‖ - ‖b‖ := by linarith [CD.hbeta_bound, CD.hgamma_bound]
      _ ≤ ‖a + b‖ := hrev
  have hCS_B : ‖l2Inner main CD.Psi‖ ≤ l2Norm main * CD.B :=
    calc ‖l2Inner main CD.Psi‖
        ≤ l2Norm main * l2Norm CD.Psi := cauchy_schwarz_l2 main CD.Psi
      _ ≤ l2Norm main * CD.B := by
          exact mul_le_mul_of_nonneg_left CD.hnorm (Real.sqrt_nonneg _)
  have h1 : (1 - CD.lambda) * CD.beta ≤ l2Norm main * CD.B := by linarith
  have hB_pos := CD.hB_pos
  have h2 : (1 - CD.lambda) * CD.beta / CD.B ≤ l2Norm main :=
    (div_le_iff₀ hB_pos).mpr h1
  have h_lhs_nn : 0 ≤ (1 - CD.lambda) * CD.beta / CD.B :=
    div_nonneg (mul_nonneg (by linarith [CD.hlambda_lt_one]) (le_of_lt CD.hbeta_pos))
               (le_of_lt CD.hB_pos)
  have h_rhs_nn : 0 ≤ l2Norm main := Real.sqrt_nonneg _
  have h3 : ((1 - CD.lambda) * CD.beta / CD.B) ^ 2 ≤ l2Norm main ^ 2 :=
    sq_le_sq' (by linarith) h2
  have h4 : l2Norm main ^ 2 = l2NormSq main := by
    unfold l2Norm; exact Real.sq_sqrt (l2NormSq_nonneg main)
  calc ((1 - CD.lambda) ^ 2 * CD.beta ^ 2) / CD.B ^ 2
      = ((1 - CD.lambda) * CD.beta / CD.B) ^ 2 := by ring
    _ ≤ l2Norm main ^ 2 := h3
    _ = l2NormSq main := h4

-- ═══════════════════════════════════════════════════════════
-- §9. Corollaires FERMÉS
-- ═══════════════════════════════════════════════════════════

omit [DecidableEq X] in
/-- Version normalisée du bridge lorsque `B = 1`. -/
theorem bridge_lower_bound_normalized
    (main : X → ℂ)
    (CD : CertificateData (X := X))
    (hsplit : ∀ x, main x = CD.diag x + CD.off x)
    (hB : CD.B = 1) :
    (1 - CD.lambda) ^ 2 * CD.beta ^ 2 ≤ l2NormSq main := by
  have h := bridge_lower_bound (X := X) main CD hsplit
  have hB2 : CD.B ^ 2 = 1 := by rw [hB]; norm_num
  rw [hB2, div_one] at h
  exact h

omit [DecidableEq X] in
/-- Corollaire demi-contrôle : si `B = 1` et `lambda ≤ 1/2`,
alors `beta²/4 ≤ l2NormSq main`. -/
theorem bridge_lower_bound_half
    (main : X → ℂ)
    (CD : CertificateData (X := X))
    (hsplit : ∀ x, main x = CD.diag x + CD.off x)
    (hB : CD.B = 1)
    (hlam : CD.lambda ≤ 1 / 2) :
    CD.beta ^ 2 / 4 ≤ l2NormSq main := by
  have h := bridge_lower_bound_normalized (X := X) main CD hsplit hB
  nlinarith [sq_nonneg CD.beta, sq_nonneg (1 - CD.lambda - 1 / 2)]

-- ═══════════════════════════════════════════════════════════
-- Garde épistémique
-- ═══════════════════════════════════════════════════════════

/-- Drapeau doctrinal : aucune revendication RH dans ce fichier. -/
def RHClaimed : Bool := false

/-- Vérification du drapeau doctrinal. -/
theorem rh_not_claimed : RHClaimed = false := rfl

end CouretUnification.Logic.H3.L10Bridge
