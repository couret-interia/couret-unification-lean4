/-
# ResGold/L1_ConductorOne.lean

**Opérateur conducteur 1** M_{p,R}^{(1),0}.

Construction : convolution multiplicative centrée sur 𝔽_p^×, diagonale
en base de caractères de Dirichlet.

## Résultats clés

* Spectre conducteur 1, modes propres χ
* Norme de Hilbert–Schmidt : ‖M^{(1),0}‖²_HS = (p-2)/(p-1)²
* Trace signée à **trois cas** (correction §15 du rapport)

## Statut

* Définitions et énoncés spectraux finis : [D]
* Identité Tamagawa locale (‖M‖²_HS = ‖Ψ‖²_{L²(ℚ_p^×)}) : [D]
  en tant qu'identité de mesures ; le mot « Tamagawa » sera réservé
  au niveau global

## v38.5 — Correction anti-True-énoncé

Les versions antérieures de ce fichier portaient `signedTrace_spec : True`
et `psi_L2_eq_HSnorm : True`. Ces énoncés sont *trivialement habitables*
par `trivial` et ne disent rien mathématiquement. Ils ont été remplacés
par des énoncés substantiels.

La connexion avec la somme spectrale Σ_χ conductorOneEigenvalue χ requiert
`Fintype (FiniteMulChar p)`, non construit dans ce module. Elle est
explicitement reportée à un module ultérieur `SpectralEnumeration.lean`.

## Note pour Thomas

Les `sorry` sont tous des calculs spectraux finis sur des espaces
de dimension p - 1 ; rien d'analytique. Le verrou ici est purement
de présentation Lean (choix de représentation matricielle vs
fonctionnelle des caractères).
-/

import Mathlib.Tactic
import CouretUnification.ResGold.L0_LocalLemma

namespace CouretUnification.ResGold.L1

open Finset BigOperators ResGold.L0

variable (p : ℕ) [hp : Fact p.Prime]

/-- Fonction ResGold centrée sur 𝔽_p^× :
    ψ_{p,R}(a) = φ_{p,R}(a) - I_p^quot(R). -/
noncomputable def psi (R : ZMod p) (a : ZMod p) : ℂ :=
  (localPhi p R a : ℂ) - (Ip_quotient p R : ℂ)

/-- Valeur propre du mode de caractère χ pour l'opérateur de convolution.
**[D]**

Convention : λ_χ = (1/(p-1)) · J_p(R, χ^{-1}).
* χ = 1   : λ_1 = ν_p(R)/(p-1) = I_p^quot(R)
* χ ≠ 1, R = 0 : λ_χ = 0
* χ ≠ 1, R ≠ 0 : λ_χ = -χ(R)^{-1}/(p-1)

Pour l'opérateur **centré** M^{(1),0}, le mode trivial λ_1 est mis à zéro. -/
noncomputable def conductorOneEigenvalue (R : ZMod p) (χ : FiniteMulChar p) : ℂ := by
  classical
  exact
    if χ = trivChar p then 0  -- mode trivial annulé par centrage
    else if R = 0 then 0
    else -(χ R) / (p - 1 : ℂ)
  -- convention χ ↔ χ^{-1} à fixer côté Thomas si nécessaire

/-- **[D]** Carré du module des valeurs propres non triviales.

Pour χ ≠ 1, R ≠ 0 : |λ_χ|² = 1/(p-1)². -/
theorem conductorOneEigenvalue_abs_sq (R : ZMod p) (χ : FiniteMulChar p)
    (hχ : χ ≠ trivChar p) (hR : R ≠ 0) :
    Complex.normSq (conductorOneEigenvalue p R χ) = 1 / ((p - 1 : ℝ) ^ 2) := by
  classical

  have hden_norm :
      Complex.normSq ((p : ℂ) - 1) = ((p : ℝ) - 1) ^ 2 := by
    simpa [pow_two] using (Complex.normSq_ofReal ((p : ℝ) - 1))

  unfold conductorOneEigenvalue
  simp [hχ, hR, χ.normSq_nonzero R hR, hden_norm, pow_two]

/-- **[D]** Norme de Hilbert–Schmidt au carré de l'opérateur centré.

‖M_{p,R}^{(1),0}‖²_HS = (p-2)/(p-1)²  si R ≠ 0
                     = 0              si R = 0

Preuve : somme des |λ_χ|² sur les p - 2 caractères non triviaux,
chacun contribuant 1/(p-1)². -/
noncomputable def HSnorm_sq (R : ZMod p) : ℝ :=
  if R = 0 then 0
  else ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2

omit hp in
/-- **[D]** Identité de norme HS (tautologique de la définition).

    Ce lemme ne dépend pas de l'hypothèse de primalité `hp`. -/
theorem HSnorm_sq_eq (R : ZMod p) :
    HSnorm_sq p R =
      if R = 0 then 0
      else ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  rfl

/-- **[D]** Trace signée — formule à **trois cas**.

Correction §15 du rapport : le cas R ≡ 1 (mod p) bifurque.

* p ∣ R                              : Tr = 0
* R ≡ 1 (mod p)                      : Tr = -(p-2)/(p-1)
* p ∤ R et R ≢ 1 (mod p)             : Tr = 1/(p-1)

Preuve (esquisse) :
Tr M = Σ_{χ ≠ 1} λ_χ = -1/(p-1) · Σ_{χ ≠ 1} χ(R).
Or Σ_{χ ≠ 1} χ(g) = (p-1) - 1 = p - 2 si g = 1, sinon -1.
D'où les trois cas. -/
noncomputable def signedTrace (R : ZMod p) : ℂ :=
  if R = 0 then 0
  else if R = 1 then -((p : ℂ) - 2) / ((p : ℂ) - 1)
  else 1 / ((p : ℂ) - 1)

/-- **[D]** Caractérisation cas-par-cas de la trace signée.

Cet énoncé est tautologique de la définition de `signedTrace`, mais il
fixe explicitement la structure à trois cas et empêche tout refactor
silencieux de la définition.

**Note v38.5.** L'énoncé porte le *contenu* (trois cas explicites), pas
juste `True`. Si la définition de `signedTrace` change, ce théorème
casse et alerte. -/
theorem signedTrace_three_cases (R : ZMod p) :
    (R = 0 → signedTrace p R = 0) ∧
    (R ≠ 0 → R = 1 → signedTrace p R = -((p : ℂ) - 2) / ((p : ℂ) - 1)) ∧
    (R ≠ 0 → R ≠ 1 → signedTrace p R = 1 / ((p : ℂ) - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hR0
    unfold signedTrace
    rw [if_pos hR0]
  · intro hR0 hR1
    unfold signedTrace
    rw [if_neg hR0, if_pos hR1]
  · intro hR0 hR1
    unfold signedTrace
    rw [if_neg hR0, if_neg hR1]

/-- **[O]** Statut documentaire : connexion entre `signedTrace` et la
    somme spectrale Σ_χ conductorOneEigenvalue χ.

Cette connexion est démontrable mathématiquement (orthogonalité des
caractères + définition de conductorOneEigenvalue), mais sa formalisation Lean
demande `Fintype (FiniteMulChar p)`, non construit ici.

Module ultérieur : `ResGold/SpectralEnumeration.lean` (à créer). -/
def signedTrace_spectral_sum_status : ResGoldStatus := ResGoldStatus.O

/-- **[D]** Identité de norme L² au niveau quotient fini :

    (1/(p-1)) · Σ_{a ∈ (ZMod p)^×} |ψ_{p,R}(a)|² = ‖M‖²_HS.

Cette identité, démontrée par calcul direct, est l'**ingrédient local**
qui sera relu (au niveau global) comme identité Tamagawa une fois la
mesure adélique en place. À ce stade, c'est uniquement une identité
de normalisations finies.

**Calcul (esquisse pour Thomas) :**

* Si R = 0 : ψ_{p,0}(a) = φ_{p,0}(a) - I_p^quot(0) = 𝟙[a≠0] - 1 = 0
  pour a ≠ 0. Somme = 0. HSnorm_sq = 0. OK.

* Si R ≠ 0 :
  - a = R (un cas, R ∈ (ZMod p)^×) : ψ = 0 - (p-2)/(p-1) = -(p-2)/(p-1).
    |ψ|² = (p-2)²/(p-1)².
  - a ≠ 0, a ≠ R (p-2 cas) : ψ = 1 - (p-2)/(p-1) = 1/(p-1).
    |ψ|² = 1/(p-1)².
  - Somme : (p-2)²/(p-1)² + (p-2)·1/(p-1)² = (p-2)·(p-1)/(p-1)² = (p-2)/(p-1).
  - Divisé par (p-1) : (p-2)/(p-1)². OK.

**Note v38.5.** L'énoncé porte l'identité réelle entre la norme L² de ψ
et la norme HS, pas `True`. Le `sorry` est sur une preuve dont
l'esquisse est ci-dessus. -/
theorem psi_L2_eq_HSnorm (R : ZMod p) :
    (∑ a ∈ (Finset.univ : Finset (ZMod p)).filter (fun a => a ≠ 0),
        Complex.normSq (psi p R a))
      / ((p : ℝ) - 1) = HSnorm_sq p R := by
  classical

  let U : Finset (ZMod p) :=
    (Finset.univ : Finset (ZMod p)).filter (fun a => a ≠ 0)

  change
    (Finset.sum U (fun a => Complex.normSq (psi p R a)))
      / ((p : ℝ) - 1) = HSnorm_sq p R

  have hp2 : 2 ≤ p := hp.out.two_le
  have hp1 : 1 ≤ p := by omega

  have hden : (p : ℝ) - 1 ≠ 0 := by
    have hpgt : (1 : ℝ) < p := by
      exact_mod_cast hp.out.one_lt
    linarith

  by_cases hR : R = 0

  · have hsum_zero :
        Finset.sum U (fun a => Complex.normSq (psi p R a)) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have ha0 : a ≠ 0 := by
        simpa [U] using ha
      subst R
      unfold psi localPhi
      rw [Ip_quotient_eq]
      simp [ha0]

    unfold HSnorm_sq
    rw [if_pos hR, hsum_zero]
    simp

  · have hI_complex :
        ((Ip_quotient p R : ℚ) : ℂ) =
          (((p : ℝ) - 2) / ((p : ℝ) - 1) : ℂ) := by
      rw [Ip_quotient_eq]
      simp [hR]
      norm_num [Nat.cast_sub hp2, Nat.cast_sub hp1]

    have hRmem : R ∈ U := by
      simp [U, hR]

    have hU_eq :
        U = ((Finset.univ : Finset (ZMod p)).erase (0 : ZMod p)) := by
      ext a
      by_cases ha : a = 0
      · subst a
        simp [U]
      · simp [U, ha]

    have hcardU : U.card = p - 1 := by
      rw [hU_eq]
      rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p))]
      simp

    have hcard_rest : (U.erase R).card = p - 2 := by
      rw [Finset.card_erase_of_mem hRmem, hcardU]
      omega

    have hpsi_R_val :
        psi p R R =
          (-(((p : ℝ) - 2) / ((p : ℝ) - 1)) : ℂ) := by
      unfold psi localPhi
      rw [hI_complex]
      simp [hR]

    have hpsi_R_norm :
        Complex.normSq (psi p R R) =
          (((p : ℝ) - 2) / ((p : ℝ) - 1)) ^ 2 := by
      rw [hpsi_R_val]
      simpa [pow_two] using
        (Complex.normSq_ofReal (-(((p : ℝ) - 2) / ((p : ℝ) - 1))))

    have hreal_other :
        (1 : ℝ) - (((p : ℝ) - 2) / ((p : ℝ) - 1)) =
          1 / ((p : ℝ) - 1) := by
      field_simp [hden]
      ring

    have hpsi_other :
        ∀ a ∈ U.erase R,
          Complex.normSq (psi p R a) =
            (1 / ((p : ℝ) - 1)) ^ 2 := by
      intro a ha
      have haU : a ∈ U := (Finset.mem_erase.mp ha).2
      have haR : a ≠ R := (Finset.mem_erase.mp ha).1
      have ha0 : a ≠ 0 := by
        simpa [U] using haU
      have hsub : R - a ≠ 0 := by
        intro hz
        exact haR ((sub_eq_zero.mp hz).symm)

      have hpsi_val :
          psi p R a = ((1 / ((p : ℝ) - 1) : ℝ) : ℂ) := by
        calc
          psi p R a
              =
            (1 : ℂ) -
              ((((p : ℝ) - 2) / ((p : ℝ) - 1) : ℝ) : ℂ) := by
                unfold psi localPhi
                rw [hI_complex]
                simp [ha0, hsub]
          _ =
            (((1 : ℝ) - (((p : ℝ) - 2) / ((p : ℝ) - 1)) : ℝ) : ℂ) := by
                simp
          _ =
            ((1 / ((p : ℝ) - 1) : ℝ) : ℂ) := by
                rw [hreal_other]

      rw [hpsi_val]
      simpa [pow_two] using
        (Complex.normSq_ofReal (1 / ((p : ℝ) - 1)))

    have hsum_rest :
        Finset.sum (U.erase R) (fun a => Complex.normSq (psi p R a)) =
          ((p : ℝ) - 2) * (1 / ((p : ℝ) - 1)) ^ 2 := by
      calc
        Finset.sum (U.erase R) (fun a => Complex.normSq (psi p R a))
            =
          Finset.sum (U.erase R)
            (fun _ => (1 / ((p : ℝ) - 1)) ^ 2) := by
              apply Finset.sum_congr rfl
              intro a ha
              exact hpsi_other a ha
        _ = ((U.erase R).card : ℝ) * (1 / ((p : ℝ) - 1)) ^ 2 := by
              simp
        _ = ((p : ℝ) - 2) * (1 / ((p : ℝ) - 1)) ^ 2 := by
              rw [hcard_rest]
              norm_num [Nat.cast_sub hp2]

    have hsplit :=
      Finset.sum_erase_add
        (s := U)
        (a := R)
        (f := fun a : ZMod p => Complex.normSq (psi p R a))
        hRmem

    have hsum_total :
        Finset.sum U (fun a => Complex.normSq (psi p R a)) =
          ((p : ℝ) - 2) * (1 / ((p : ℝ) - 1)) ^ 2
            + (((p : ℝ) - 2) / ((p : ℝ) - 1)) ^ 2 := by
      calc
        Finset.sum U (fun a => Complex.normSq (psi p R a))
            =
          Finset.sum (U.erase R) (fun a => Complex.normSq (psi p R a))
            + Complex.normSq (psi p R R) := by
              exact hsplit.symm
        _ =
          ((p : ℝ) - 2) * (1 / ((p : ℝ) - 1)) ^ 2
            + (((p : ℝ) - 2) / ((p : ℝ) - 1)) ^ 2 := by
              rw [hsum_rest, hpsi_R_norm]

    rw [hsum_total]
    unfold HSnorm_sq
    rw [if_neg hR]
    field_simp [hden]
    ring_nf

end CouretUnification.ResGold.L1
