/-
# ResGold/L0_LocalLemma.lean

**AdelicLocalLemma** — résultat ResGold-L0.

Énoncé central :
  I_p(R) = ν_p(R) / (p - 1)
où ν_p(R) = (p - 1) si p ∣ R, sinon (p - 2).

## Statut par bloc

* `localPhi`, `nu`         : définitions finies, [D]
* `nu_value`               : identité combinatoire, [D] (provable, sorry routinier)
* `Jcal`, `Jcal_one`,
  `Jcal_nontrivial`        : décomposition Dirichlet multiplicative, [D]
* `Ip_quotient`            : valeur rationnelle ν_p(R)/(p-1), [D]
* `Ip_padic_integral`      : identité avec intégrale p-adique, [H]
  (nécessite Haar sur ℚ_p^× normalisée μ^×(ℤ_p^×) = 1 ; à wirer côté Mathlib)

## Discipline v38.5

Tous les `sorry` portent des énoncés substantiels (pas de True). Tous les
sorries sont annotés [D, provable] ou [H]. Aucun axiom. Aucun sorry au
niveau d'une constante non-conditionnelle.

## Note pour Thomas

Les `sorry` marqués [D, provable] sont des cas d'analyse finie sur
`Finset.filter` ; ils devraient compiler avec `decide` ou `Finset.card_eq_*`
après dépliage. Les `sorry` marqués [H] reflètent un travail de mesure
p-adique pas encore disponible directement dans Mathlib v4.29.1 et
demandent une décision d'architecture côté Lean (voir module ultérieur
`ResGold/PadicMeasure.lean` à créer).

## Décision d'architecture (Décision 1)

Position du programme : le quotient combinatoire fini `Ip_quotient` suffit
pour L1 et L2. L'égalité avec l'intégrale p-adique réelle est reportée
à un module séparé. Cette séparation suit la discipline FROZEN/ACTIVE v36 :
le module ResGold principal reste indépendant du wiring p-adique.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Finite.Basic
import CouretUnification.ResGold.Status

namespace CouretUnification.ResGold.L0

open Finset BigOperators

variable (p : ℕ) [hp : Fact p.Prime]

/-- ResGold local indicator on 𝔽_p :
    φ_{p,R}(a) = 1 si a ≠ 0 et R - a ≠ 0, sinon 0. -/
def localPhi (R a : ZMod p) : ℕ :=
  if a ≠ 0 ∧ R - a ≠ 0 then 1 else 0

/-- Local count :
    ν_p(R) = #{a ∈ ZMod p : a ≠ 0 ∧ R - a ≠ 0}. -/
def nu (R : ZMod p) : ℕ :=
  ((Finset.univ : Finset (ZMod p)).filter
    (fun a => a ≠ 0 ∧ R - a ≠ 0)).card

/-- **[D]** Identité combinatoire fondamentale :
    ν_p(R) = (p - 1) si R = 0, sinon (p - 2). -/
theorem nu_value (R : ZMod p) :
    nu p R = if R = 0 then p - 1 else p - 2 := by
  classical
  unfold nu
  have hcard : (Finset.univ : Finset (ZMod p)).card = p := by
    simp
  by_cases hR : R = 0
  · rw [if_pos hR]
    subst R
    have hfilter :
        ((Finset.univ : Finset (ZMod p)).filter
          (fun a => a ≠ 0 ∧ (0 : ZMod p) - a ≠ 0))
          =
        ((Finset.univ : Finset (ZMod p)).erase 0) := by
      ext a
      by_cases ha : a = 0 <;> simp [ha]
    rw [hfilter]
    rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p))]
    rw [hcard]
  · rw [if_neg hR]
    have hfilter :
        ((Finset.univ : Finset (ZMod p)).filter
          (fun a => a ≠ 0 ∧ R - a ≠ 0))
          =
        (((Finset.univ : Finset (ZMod p)).erase 0).erase R) := by
      ext a
      by_cases ha0 : a = 0
      · subst a
        simp [hR]
      · by_cases haR : a = R
        · subst a
          simp [hR]
        · have hsub : R - a ≠ 0 := by
            intro hz
            exact haR ((sub_eq_zero.mp hz).symm)
          simp [ha0, haR, hsub]
    rw [hfilter]
    have hRmem : R ∈ ((Finset.univ : Finset (ZMod p)).erase 0) := by
      simp [hR]
    rw [Finset.card_erase_of_mem hRmem]
    rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p))]
    rw [hcard]
    have hp2 : 2 ≤ p := hp.out.two_le
    omega

/-- Caractère multiplicatif sur (ZMod p)^×, étendu par 0 hors des unités.
Convention abstraite : on suppose χ : ZMod p → ℂ avec χ 0 = 0,
χ (a * b) = χ a * χ b sur les unités, et χ 1 = 1.

**Note v38.3** : tous les champs sont effectifs (pas de Prop nues).
Le champ `toFun` est la donnée fonctionnelle ; `zero`, `mul`, `one`
sont des contraintes effectives sur cette donnée. -/
structure FiniteMulChar (p : ℕ) [Fact p.Prime] where
  toFun : ZMod p → ℂ
  zero : toFun 0 = 0
  mul : ∀ a b : ZMod p, a ≠ 0 → b ≠ 0 → toFun (a * b) = toFun a * toFun b
  one : toFun 1 = 1

instance : CoeFun (FiniteMulChar p) (fun _ => ZMod p → ℂ) :=
  ⟨FiniteMulChar.toFun⟩

/-- Extensionalité fonctionnelle pour les caractères multiplicatifs finis.

Les champs `zero`, `mul`, `one` sont propositionnels ; deux caractères sont
égaux dès que leurs fonctions sous-jacentes sont égales. -/
@[ext]
theorem FiniteMulChar.ext_toFun {χ ψ : FiniteMulChar p}
    (h : ∀ a : ZMod p, χ a = ψ a) : χ = ψ := by
  cases χ with
  | mk f fzero fmul fone =>
    cases ψ with
    | mk g gzero gmul gone =>
      have hfg : f = g := funext h
      cases hfg
      congr

/-- Caractère trivial : χ_1(a) = 1 si a ≠ 0, sinon 0. -/
def trivChar : FiniteMulChar p where
  toFun a := if a = 0 then 0 else 1
  zero := by simp
  mul := by intro a b ha hb; simp [ha, hb, mul_ne_zero ha hb]
  one := by simp

/-- Somme de caractères J_p(R, χ) = Σ_a φ(a) χ(a). -/
def Jcal (R : ZMod p) (χ : FiniteMulChar p) : ℂ :=
  ∑ a, (localPhi p R a : ℂ) * χ a

/-- **[D]** Caractère trivial : J_p(R, 1) = ν_p(R). -/
theorem Jcal_one (R : ZMod p) :
    Jcal p R (trivChar p) = (nu p R : ℂ) := by
  classical
  unfold Jcal nu
  have hsum :
      (∑ a : ZMod p, (localPhi p R a : ℂ) * (trivChar p) a)
        =
      ∑ a : ZMod p, if a ≠ 0 ∧ R - a ≠ 0 then (1 : ℂ) else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : a ≠ 0 ∧ R - a ≠ 0
    · simp [localPhi, trivChar, h]
    · simp [localPhi, trivChar, h]
  rw [hsum]
  rw [← Finset.sum_filter]
  simp

/-- Somme totale d’un caractère multiplicatif non trivial sur `ZMod p`.

Orthogonalité finie :
si `χ c ≠ 1`, alors la multiplication par `c` permute `ZMod p`, donc

`S = ∑ a, χ a = ∑ a, χ (c * a) = χ c * S`

et donc `S = 0`. -/
private theorem char_sum_eq_zero (χ : FiniteMulChar p)
    (hχ : χ ≠ trivChar p) :
    (∑ a : ZMod p, χ a) = 0 := by
  classical

  have h_exists : ∃ c : ZMod p, c ≠ 0 ∧ χ c ≠ 1 := by
    by_contra hnone
    apply hχ
    apply FiniteMulChar.ext_toFun
    intro a
    by_cases ha : a = 0
    · subst a
      simp [trivChar, χ.zero]
    · have hχa : χ a = 1 := by
        by_contra hbad
        exact hnone ⟨a, ha, hbad⟩
      simp [trivChar, ha, hχa]

  rcases h_exists with ⟨c, hc0, hc1⟩

  have hperm :
      (∑ a : ZMod p, χ (c * a)) = ∑ a : ZMod p, χ a := by
    refine Finset.sum_bij
      (fun a _ => c * a)
      ?hmem
      ?hinj
      ?hsurj
      ?hval
    · intro a _
      simp
    · intro a₁ _ a₂ _ hmul
      have hmul' := congrArg (fun x : ZMod p => c⁻¹ * x) hmul
      calc
        a₁ = 1 * a₁ := by simp
        _ = (c⁻¹ * c) * a₁ := by rw [inv_mul_cancel₀ hc0]
        _ = c⁻¹ * (c * a₁) := by rw [mul_assoc]
        _ = c⁻¹ * (c * a₂) := hmul'
        _ = (c⁻¹ * c) * a₂ := by rw [mul_assoc]
        _ = 1 * a₂ := by rw [inv_mul_cancel₀ hc0]
        _ = a₂ := by simp
    · intro b _
      refine ⟨c⁻¹ * b, by simp, ?_⟩
      calc
        c * (c⁻¹ * b) = (c * c⁻¹) * b := by rw [mul_assoc]
        _ = 1 * b := by rw [mul_inv_cancel₀ hc0]
        _ = b := by simp
    · intro a _
      rfl

  have hmul_all : ∀ a : ZMod p, χ (c * a) = χ c * χ a := by
    intro a
    by_cases ha : a = 0
    · subst a
      simp [χ.zero]
    · exact χ.mul c a hc0 ha

  have hscale :
      (∑ a : ZMod p, χ (c * a)) =
        χ c * (∑ a : ZMod p, χ a) := by
    calc
      (∑ a : ZMod p, χ (c * a))
          = ∑ a : ZMod p, χ c * χ a := by
              apply Finset.sum_congr rfl
              intro a _
              exact hmul_all a
      _ = χ c * (∑ a : ZMod p, χ a) := by
              rw [Finset.mul_sum]

  have hfixed :
      (∑ a : ZMod p, χ a) =
        χ c * (∑ a : ZMod p, χ a) := by
    calc
      (∑ a : ZMod p, χ a)
          = ∑ a : ZMod p, χ (c * a) := hperm.symm
      _ = χ c * (∑ a : ZMod p, χ a) := hscale

  have hzero :
      (χ c - 1) * (∑ a : ZMod p, χ a) = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr hfixed.symm

  have hcne : χ c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  exact (mul_eq_zero.mp hzero).resolve_left hcne


/-- Version avec `0` retiré. Comme `χ 0 = 0`, c’est la même somme. -/
private theorem char_sum_erase_zero_eq_zero (χ : FiniteMulChar p)
    (hχ : χ ≠ trivChar p) :
    Finset.sum ((Finset.univ : Finset (ZMod p)).erase (0 : ZMod p))
      (fun a => χ a) = 0 := by
  classical
  have htot := char_sum_eq_zero p χ hχ

  have hsplit :=
    Finset.sum_erase_add
      (s := (Finset.univ : Finset (ZMod p)))
      (a := (0 : ZMod p))
      (f := fun a : ZMod p => χ a)
      (Finset.mem_univ (0 : ZMod p))

  have h :
      Finset.sum ((Finset.univ : Finset (ZMod p)).erase (0 : ZMod p))
        (fun a => χ a) + χ 0 = 0 := by
    rw [hsplit, htot]

  simpa [χ.zero] using h


/-- Réécriture de `Jcal` comme somme filtrée des valeurs de `χ`. -/
private theorem Jcal_eq_filter (R : ZMod p) (χ : FiniteMulChar p) :
    Jcal p R χ =
      Finset.sum
        ((Finset.univ : Finset (ZMod p)).filter
          (fun a => a ≠ 0 ∧ R - a ≠ 0))
        (fun a => χ a) := by
  classical
  unfold Jcal
  calc
    (∑ a : ZMod p, (localPhi p R a : ℂ) * χ a)
        = ∑ a : ZMod p,
            if a ≠ 0 ∧ R - a ≠ 0 then χ a else 0 := by
              apply Finset.sum_congr rfl
              intro a _
              by_cases h : a ≠ 0 ∧ R - a ≠ 0
              · simp [localPhi, h]
              · simp [localPhi, h]
    _ =
      Finset.sum
        ((Finset.univ : Finset (ZMod p)).filter
          (fun a => a ≠ 0 ∧ R - a ≠ 0))
        (fun a => χ a) := by
          rw [← Finset.sum_filter]

/-- **[D]** Caractère non trivial :
    J_p(R, χ) = 0 si R = 0, sinon -χ(R). -/
theorem Jcal_nontrivial (R : ZMod p) (χ : FiniteMulChar p)
    (hχ : χ ≠ trivChar p) :
    Jcal p R χ = if R = 0 then 0 else -χ R := by
  classical

  by_cases hR : R = 0
  · rw [if_pos hR]
    subst R
    rw [Jcal_eq_filter]

    have hfilter :
        ((Finset.univ : Finset (ZMod p)).filter
          (fun a => a ≠ 0 ∧ (0 : ZMod p) - a ≠ 0))
          =
        ((Finset.univ : Finset (ZMod p)).erase (0 : ZMod p)) := by
      ext a
      by_cases ha : a = 0
      · subst a
        simp
      · simp [ha]

    rw [hfilter]
    exact char_sum_erase_zero_eq_zero p χ hχ

  · rw [if_neg hR]
    rw [Jcal_eq_filter]

    have hfilter :
        ((Finset.univ : Finset (ZMod p)).filter
          (fun a => a ≠ 0 ∧ R - a ≠ 0))
          =
        (((Finset.univ : Finset (ZMod p)).erase (0 : ZMod p)).erase R) := by
      ext a
      by_cases ha0 : a = 0
      · subst a
        simp [hR]
      · by_cases haR : a = R
        · subst a
          simp [hR]
        · have hsub : R - a ≠ 0 := by
            intro hz
            exact haR ((sub_eq_zero.mp hz).symm)
          simp [ha0, haR, hsub]

    rw [hfilter]

    have hnonzero_sum :
        Finset.sum ((Finset.univ : Finset (ZMod p)).erase (0 : ZMod p))
          (fun a => χ a) = 0 :=
      char_sum_erase_zero_eq_zero p χ hχ

    have hRmem :
        R ∈ ((Finset.univ : Finset (ZMod p)).erase (0 : ZMod p)) := by
      simp [hR]

    have hsplit :=
      Finset.sum_erase_add
        (s := ((Finset.univ : Finset (ZMod p)).erase (0 : ZMod p)))
        (a := R)
        (f := fun a : ZMod p => χ a)
        hRmem

    have herased :
        Finset.sum
          (((Finset.univ : Finset (ZMod p)).erase (0 : ZMod p)).erase R)
          (fun a => χ a) + χ R = 0 := by
      rw [hsplit, hnonzero_sum]

    calc
      Finset.sum
          (((Finset.univ : Finset (ZMod p)).erase (0 : ZMod p)).erase R)
          (fun a => χ a)
          =
        Finset.sum
          (((Finset.univ : Finset (ZMod p)).erase (0 : ZMod p)).erase R)
          (fun a => χ a) + χ R - χ R := by
            simp
      _ = 0 - χ R := by rw [herased]
      _ = -χ R := by simp

/-- **[D]** Valeur rationnelle de l'intégrale au niveau du quotient fini :
    I_p^quot(R) = ν_p(R) / (p - 1).

Cette valeur ne dépend que de la combinatoire finie. -/
noncomputable def Ip_quotient (R : ZMod p) : ℚ :=
  (nu p R : ℚ) / (p - 1 : ℚ)

/-- **[D]** Identité rationnelle. -/
theorem Ip_quotient_eq (R : ZMod p) :
    Ip_quotient p R = if R = 0 then 1 else (p - 2 : ℚ) / (p - 1 : ℚ) := by
  classical
  unfold Ip_quotient
  rw [nu_value]

  by_cases hR : R = 0
  · simp [hR]

    have hp1 : 1 ≤ p := by
      have hp2 : 2 ≤ p := hp.out.two_le
      omega

    have hnum :
        ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
      rw [Nat.cast_sub hp1]
      simp

    have hden : (p : ℚ) - 1 ≠ 0 := by
      intro h
      have hpq : (p : ℚ) = 1 := sub_eq_zero.mp h
      have hpnat : p = 1 := by
        exact Nat.cast_inj.mp (by simpa using hpq)
      have hp2 : 2 ≤ p := hp.out.two_le
      omega

    rw [hnum]
    exact div_self hden

  · simp [hR]

    have hp2 : 2 ≤ p := hp.out.two_le

    rw [Nat.cast_sub hp2]
    simp

/-- **[H]** Statut de l'identité avec l'intégrale p-adique :
    I_p(R) = ν_p(R) / (p - 1)
où I_p est l'intégrale p-adique sous la mesure de Haar multiplicative
normalisée μ^×(ℤ_p^×) = 1.

Cette identité est **démontrée mathématiquement** dans le rapport
(section 9). Le statut [H] reflète une lacune de **bibliothèque Lean** :
l'intégrale p-adique normalisée n'est pas directement disponible dans
Mathlib v4.29.1 sous une forme utilisable.

**Décision d'architecture** : le quotient combinatoire `Ip_quotient`
suffit pour les usages ultérieurs (L1, L2) ; l'égalité avec l'intégrale
p-adique réelle est reportée à un module séparé `ResGold/PadicMeasure.lean`
à créer ultérieurement.

**Note** : ce n'est pas un théorème mais un marqueur documentaire.
Aucun `True` placeholder ici. La discipline v38.5 anti-True-énoncé est
respectée par le choix de typer comme `ResGoldStatus` plutôt que `Prop`. -/
def Ip_padic_integral_status : ResGoldStatus := ResGoldStatus.H

end CouretUnification.ResGold.L0
