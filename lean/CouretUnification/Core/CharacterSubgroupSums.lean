import CouretUnification.Core.CharacterLemmas
import Mathlib.Tactic

/-!
# Sommes de caractères sur un sous-groupe (cas ordre 2)

Couret–Unification — couche abstraite, étage B.
Préalable au lemme du défaut ponctuel (`PointDefectLemma.lean`).

## STATUT : [P-scaffold] — NON COMPILÉ côté rédaction (pas d'environnement Lean).
Objectif visé : 0 sorry. Les `sorry` résiduels sont des pas MÉCANIQUES ou des appels
à l'orthogonalité globale (résultat Mathlib standard) ; ils ne cachent aucun trou
conceptuel. Le premier `lake build` de Thomas sert de révélateur pour la syntaxe
Mathlib (noms de lemmes, coercions ℂˣ→ℂ, décidabilité de l'appartenance au noyau).

## Contenu

- `char_val_eq_one_or_neg_one` : un caractère d'ordre 2 prend ses valeurs dans {1, −1}.
- `quadraticProjectorC_eq_kerIndicatorC` : P_χ(x) = ½(1 + χ(x)) = 1_{ker χ}(x).
  C'est l'identité `1_A = (1 + χ)/2` ponctuelle (le « projecteur quadratique »).
- `trivial_on_ker_iff` : pour χ d'ordre 2, caractères triviaux sur ker χ = {1, χ}.
  Preuve DIRECTE pointwise (sans QuotientGroup). [hors chemin critique, voir §3]
- `sum_over_ker_eq_zero` : Σ_{x∈ker χ} ψ(x) = 0 pour ψ ∉ {1, χ}, par la VOIE PROJECTEUR
  (somme globale pondérée → orthogonalité globale), plus propre que la translation.

## Choix de preuve (arbitré 3 juin 2026)

Deux décisions :
1. `trivial_on_ker_iff` : preuve pointwise directe, PAS QuotientGroup (χ à valeurs ±1
   donne la dichotomie G = ker χ ⊔ complément gratuitement).
2. `sum_over_ker_eq_zero` : VOIE PROJECTEUR. On écrit Σ_{x∈A} ψ = ½ Σ_G (1+χ)ψ
   = ½(Σ_G ψ + Σ_G χψ) = 0, où χψ est non trivial car χ⁻¹ = χ et ψ ≠ χ. Le cœur
   devient l'orthogonalité GLOBALE (Σ_G d'un caractère non trivial = 0), résultat
   Mathlib standard — au lieu d'une manipulation de Finset de sous-groupe par
   translation. Vérifié numériquement : pour ψ ∉ {1,χ}, Σ_G ψ = Σ_G χψ = 0.

## Cadre

Caractères abstraits `G →* ℂˣ` sur un groupe abélien fini. Spécialisation à
G₃₀ = (ℤ/30ℤ)ˣ dans `G30ClassificationFromPointDefect.lean`.

`RHClaimed = false. ScopeExpansionClaimed = false.`
-/

namespace CouretUnification.Core.CharacterSubgroupSums

open scoped BigOperators
open Classical

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-! ## §1. Valeurs d'un caractère d'ordre 2 -/

/-- Valeur du caractère vue dans ℂ. -/
def charValC (χ : G →* ℂˣ) (x : G) : ℂ := (χ x : ℂ)

/-- Si `(z:ℂ)² = 1`, alors `z = 1` ou `z = −1` (intégrité de ℂ). -/
theorem unit_sq_eq_one_imp (z : ℂˣ) (h : (z : ℂ) ^ 2 = 1) :
    (z : ℂ) = 1 ∨ (z : ℂ) = -1 := by
  have h2 : (z : ℂ) * (z : ℂ) = 1 := by rw [← sq]; exact h
  exact mul_self_eq_one_iff.mp h2

omit [Fintype G] [DecidableEq G] in
/-- Un caractère d'ordre 2 prend ses valeurs dans {1, −1}. -/
theorem char_val_eq_one_or_neg_one
    (χ : G →* ℂˣ) (hχ2 : ∀ x, (χ x : ℂ) ^ 2 = 1) (x : G) :
    (χ x : ℂ) = 1 ∨ (χ x : ℂ) = -1 :=
  unit_sq_eq_one_imp (χ x) (hχ2 x)

/-! ## §2. Projecteur quadratique = indicatrice du noyau

L'identité `1_A = (1 + χ)/2` ponctuelle. Contribution Alexandre/InterIA, 3 juin 2026.
C'est l'ingrédient qui permet de remplacer une somme sur ker χ par une somme globale
pondérée par le projecteur. -/

/-- Projecteur quadratique P_χ(x) = ½(1 + χ(x)). -/
noncomputable def quadraticProjectorC (χ : G →* ℂˣ) (x : G) : ℂ :=
  (1 + charValC χ x) / 2

/-- Indicatrice complexe du noyau de χ. -/
noncomputable def kerIndicatorC (χ : G →* ℂˣ) (x : G) : ℂ :=
  if x ∈ χ.ker then 1 else 0

omit [Fintype G] [DecidableEq G] in
/-- **Projecteur quadratique = indicatrice du noyau.**
    x ∈ ker χ ⟹ χx = 1 ⟹ P_χ(x) = ½(1+1) = 1 = 1_A(x).
    x ∉ ker χ ⟹ χx = −1 (ordre 2) ⟹ P_χ(x) = ½(1−1) = 0 = 1_A(x). -/
theorem quadraticProjectorC_eq_kerIndicatorC
    (χ : G →* ℂˣ) (hχ2 : ∀ x : G, (χ x : ℂ) ^ 2 = 1) (x : G) :
    quadraticProjectorC χ x = kerIndicatorC χ x := by
  classical
  unfold quadraticProjectorC kerIndicatorC charValC
  by_cases hx : x ∈ χ.ker
  · -- cas x ∈ ker χ : χ x = 1
    have hχx_units : χ x = 1 := by simpa [MonoidHom.mem_ker] using hx
    have hχx : (χ x : ℂ) = 1 := by rw [hχx_units]; simp
    rw [if_pos hx, hχx]; norm_num
  · -- cas x ∉ ker χ : χ x = -1
    have hχx_ne_one : (χ x : ℂ) ≠ 1 := by
      intro h; apply hx; rw [MonoidHom.mem_ker]; exact Units.ext h
    rcases char_val_eq_one_or_neg_one χ hχ2 x with hpos | hneg
    · exact absurd hpos hχx_ne_one
    · rw [if_neg hx, hneg]; norm_num

/-! ## §3. Lemme de dualité ordre 2 (preuve pointwise directe)

NOTE D'ARCHITECTURE : depuis l'adoption de la VOIE PROJECTEUR pour
`sum_over_ker_eq_zero` (§4), ce lemme n'est PLUS sur le chemin critique de la somme.
Il est conservé comme résultat structurel autonome (caractérisation des caractères
triviaux sur ker χ) et pour documenter la dualité ordre 2. -/

omit [DecidableEq G] in
/-- Pour χ d'ordre 2 non trivial, ψ est trivial sur ker χ ⟺ ψ ∈ {1, χ}.
    Preuve directe pointwise (sans QuotientGroup). -/
theorem trivial_on_ker_iff
    (χ : G →* ℂˣ) (hχ2 : ∀ x, (χ x : ℂ) ^ 2 = 1) (hχ1 : χ ≠ 1) (ψ : G →* ℂˣ) :
    (∀ x ∈ χ.ker, ψ x = 1) ↔ (ψ = 1 ∨ ψ = χ) := by
  constructor
  · intro hψA
    obtain ⟨g, hg⟩ : ∃ g, χ g ≠ 1 := by
      by_contra h; push Not at h; exact hχ1 (MonoidHom.ext h)
    have hχg : (χ g : ℂ) = -1 := by
      rcases char_val_eq_one_or_neg_one χ hχ2 g with h1 | hm1
      · exact absurd (Units.ext h1) hg
      · exact hm1
    have hg2 : g * g ∈ χ.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      have : (χ g : ℂ) * (χ g : ℂ) = 1 := by rw [hχg]; ring
      exact Units.ext (by simpa using this)
    have hψg_sq : (ψ g : ℂ) ^ 2 = 1 := by
      have hgg : ψ (g * g) = 1 := hψA _ hg2
      rw [map_mul] at hgg
      have hc : (ψ g : ℂ) * (ψ g : ℂ) = 1 := by
        have := congrArg (Units.val) hgg
        simpa [Units.val_mul] using this
      rw [sq]; exact hc
    have hψg : (ψ g : ℂ) = 1 ∨ (ψ g : ℂ) = -1 := unit_sq_eq_one_imp (ψ g) hψg_sq
    have key : ∀ x, (χ x : ℂ) = 1 → ψ x = 1 := by
      intro x hx
      exact hψA x (by rw [MonoidHom.mem_ker]; exact Units.ext (by simpa using hx))
    have key2 : ∀ x, (χ x : ℂ) = -1 → ψ x = ψ g := by
      intro x hx
      have hxg : x * g⁻¹ ∈ χ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have : (χ x : ℂ) * ((χ g : ℂ))⁻¹ = 1 := by rw [hx, hχg]; norm_num
        exact Units.ext (by
          simpa [Units.val_mul, Units.val_inv_eq_inv_val] using this)
      have hxg1 : ψ (x * g⁻¹) = 1 := hψA _ hxg
      rw [map_mul, map_inv] at hxg1
      have := mul_eq_one_iff_eq_inv.mp hxg1
      simpa using this
    rcases hψg with hpos | hneg
    · left
      apply MonoidHom.ext; intro x
      rcases char_val_eq_one_or_neg_one χ hχ2 x with hx | hx
      · exact key x hx
      · rw [key2 x hx]; exact Units.ext hpos
    · right
      apply MonoidHom.ext; intro x
      rcases char_val_eq_one_or_neg_one χ hχ2 x with hx | hx
      · rw [key x hx]; exact (Units.ext hx.symm)
      · rw [key2 x hx]
        -- ψ x = ψ g = -1 (hneg) et χ x = -1 (hx) ⟹ ψ x = χ x
        exact Units.ext (hneg.trans hx.symm)
  · rintro (rfl | rfl) x hx
    · rfl
    · rwa [MonoidHom.mem_ker] at hx

/-! ## §4. Somme nulle sur le noyau — VOIE PROJECTEUR -/

/-- Pont : somme nulle pour un caractère `G →* ℂˣ` non trivial,
    en réutilisant `CharacterLemmas.sum_char_eq_zero_of_ne_one`. -/
theorem sum_monoidHomChar_eq_zero (ξ : G →* ℂˣ) (hξ : ξ ≠ 1) :
    ∑ x : G, (ξ x : ℂ) = 0 := by
  -- composer ξ avec la coercion ℂˣ →* ℂ pour obtenir un Char G
  have hcomp : ((Units.coeHom ℂ).comp ξ) ≠ 1 := by
    intro h
    apply hξ
    -- (coeHom ∘ ξ) = 1  ⟹  ξ = 1, car la coercion ℂˣ →* ℂ est injective
    ext x
    have hx1 : (ξ x : ℂ) = 1 := by
      have := MonoidHom.ext_iff.mp h x
      simpa [MonoidHom.comp_apply, Units.coeHom_apply] using this
    -- (ξ x : ℂ) = 1 = ((1 : ℂˣ) : ℂ), et la coercion ℂˣ → ℂ est injective
    have : ξ x = 1 := Units.ext (by rw [hx1, Units.val_one])
    exact this
  -- la somme coercée = somme du Char composé
  have : ∑ x : G, (ξ x : ℂ) = ∑ x : G, ((Units.coeHom ℂ).comp ξ) x := by
    apply Finset.sum_congr rfl; intro x _
    simp [MonoidHom.comp_apply, Units.coeHom_apply]
  rw [this]
  exact CouretUnification.Core.sum_char_eq_zero_of_ne_one _ hcomp

/-- Σ_{x∈ker χ} ψ(x) = 0 pour ψ ∉ {1, χ}, par la VOIE PROJECTEUR.

    Σ_{x∈A} ψ = Σ_{x∈G} 1_A(x)·ψ(x)              (indicatrice)
              = Σ_{x∈G} ½(1 + χx)·ψx              (quadraticProjectorC_eq_kerIndicatorC)
              = ½ (Σ_G ψ + Σ_G χψ)                (distributivité)
              = ½ (0 + 0) = 0.
    χψ non trivial car χ⁻¹ = χ (ordre 2) et ψ ≠ χ. -/
theorem sum_over_ker_eq_zero
    (χ : G →* ℂˣ) (hχ2 : ∀ x, (χ x : ℂ) ^ 2 = 1) (hχ1 : χ ≠ 1)
    (ψ : G →* ℂˣ) (hψ1 : ψ ≠ 1) (hψχ : ψ ≠ χ) :
    ∑ x ∈ (χ.ker : Subgroup G).carrier.toFinset, (ψ x : ℂ) = 0 := by
  classical
  -- Étape 1 : somme sur ker = somme globale pondérée par l'indicatrice
  have step1 : ∑ x ∈ (χ.ker : Subgroup G).carrier.toFinset, (ψ x : ℂ)
      = ∑ x : G, kerIndicatorC χ x * (ψ x : ℂ) := by
    sorry  -- MÉCANIQUE : Finset.sum_filter / réindexation ker ↔ {x | x ∈ ker}.
           -- kerIndicatorC vaut 1 sur ker, 0 ailleurs.
  -- Étape 2 : indicatrice = projecteur quadratique
  have step2 : ∀ x, kerIndicatorC χ x = quadraticProjectorC χ x := fun x =>
    (quadraticProjectorC_eq_kerIndicatorC χ hχ2 x).symm
  -- Étape 3 : χψ est non trivial
  have hχψ : (χ * ψ) ≠ 1 := by
    intro h
    -- χ*ψ = 1 ⟹ ψ = χ⁻¹ = χ (ordre 2), contradiction avec ψ ≠ χ
    apply hψχ
    sorry  -- MÉCANIQUE : de χ*ψ = 1 déduire ψ = χ⁻¹, puis χ⁻¹ = χ via hχ2.
  -- Étape 4 : assemblage par orthogonalité globale
  calc ∑ x ∈ (χ.ker : Subgroup G).carrier.toFinset, (ψ x : ℂ)
      = ∑ x : G, quadraticProjectorC χ x * (ψ x : ℂ) := by
        rw [step1]; exact Finset.sum_congr rfl (fun x _ => by rw [step2])
    _ = ∑ x : G, ((1 + (χ x : ℂ)) / 2) * (ψ x : ℂ) := by
        apply Finset.sum_congr rfl; intro x _
        unfold quadraticProjectorC charValC; ring
    _ = (1/2) * (∑ x : G, (ψ x : ℂ) + ∑ x : G, ((χ x : ℂ) * (ψ x : ℂ))) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro x _; ring
    _ = (1/2) * (0 + 0) := by
        congr 1
        rw [sum_monoidHomChar_eq_zero ψ hψ1]
        have : ∑ x : G, ((χ x : ℂ) * (ψ x : ℂ)) = ∑ x : G, (((χ * ψ) x : ℂ)) := by
          apply Finset.sum_congr rfl; intro x _; simp [MonoidHom.mul_apply, Units.val_mul]
        rw [this, sum_monoidHomChar_eq_zero (χ * ψ) hχψ]
    _ = 0 := by ring

end CouretUnification.Core.CharacterSubgroupSums
