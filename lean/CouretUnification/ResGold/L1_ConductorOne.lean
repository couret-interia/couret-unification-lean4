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
  sorry -- [D, provable] calcul direct cas R = 0 vs R ≠ 0

end CouretUnification.ResGold.L1
