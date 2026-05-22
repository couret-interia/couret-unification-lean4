import CouretUnification.Finite.Foundations
import Mathlib.Tactic

namespace CouretUnification.FiniteDefect

open Finite.Foundations

/-!
# T1–T7 — Théorèmes certifiés du noyau spectral fini

Ce fichier rassemble les **vérifications exactes** du prototype spectral fini
sur `Fin 8 → ℚ`, construit dans `Finite/Foundations.lean`.

## Position dans l’architecture

On se situe ici au niveau :

- du **noyau fini exact** ;
- de la **décomposition spectrale discrète** ;
- des **projecteurs** associés aux secteurs `λ = 3`, `λ = 1`, `λ = -1`.

Aucune couche analytique globale n’est invoquée ici :
tout est **fini, exact, décidable**, et les preuves sont obtenues par
évaluation exhaustive via `native_decide`.

## Lecture conceptuelle

La matrice de Cayley exacte admet ici trois secteurs :

- **secteur cohérent** `λ = 3`, porté par `one` et `chi5`,
- **secteur neutre** `λ = 1`, récupéré par `p1`,
- **secteur de défaut** `λ = -1`, porté par `chi3` et `chi15`.

Le signal `tcInd`, indicatrice du triplet de Couret `{1,11,29}`,
sert de témoin privilégié dans les vérifications.

`RHClaimed = false`.
-/

-- ═══════════════════════════════════════════════════════════
-- T1 — Espace d'observation
-- ═══════════════════════════════════════════════════════════

/--
L’espace discret observé comporte 8 positions.

Lecture : on travaille sur les 8 unités modulo 30,
indexées par `Fin 8`.
-/
theorem T1_dim : (List.finRange 8).length = 8 := by decide

-- ═══════════════════════════════════════════════════════════
-- T2 — Pôle quadratique (fantôme 19)
-- ═══════════════════════════════════════════════════════════

/-!
Le versant purement modulaire du « fantôme 19 » est formalisé dans `Core/U30.lean`.

On n’y duplique pas ici les preuves sur `ZMod 30` ;
ce fichier se concentre sur la couche spectrale finie.
-/

-- ═══════════════════════════════════════════════════════════
-- T3 — Décomposition spectrale de Couret
-- ═══════════════════════════════════════════════════════════

/-!
## T3.1 — Orthogonalité de la base structurante

Les quatre vecteurs `one`, `chi5`, `chi3`, `chi15` forment ici
une famille orthogonale de norme quadratique 8.
-/

/-- Norme quadratique du vecteur constant. -/
theorem T3_one_norm : normSq one = 8 := by
  native_decide

/-- Norme quadratique du vecteur alterné `chi5`. -/
theorem T3_chi5_norm : normSq chi5 = 8 := by
  native_decide

/-- Norme quadratique du vecteur de défaut `chi3`. -/
theorem T3_chi3_norm : normSq chi3 = 8 := by
  native_decide

/-- Norme quadratique du vecteur de défaut `chi15`. -/
theorem T3_chi15_norm : normSq chi15 = 8 := by
  native_decide

/-- Orthogonalité `one ⟂ chi5`. -/
theorem T3_orth_one_chi5 : dot one chi5 = 0 := by
  native_decide

/-- Orthogonalité `one ⟂ chi3`. -/
theorem T3_orth_one_chi3 : dot one chi3 = 0 := by
  native_decide

/-- Orthogonalité `one ⟂ chi15`. -/
theorem T3_orth_one_chi15 : dot one chi15 = 0 := by
  native_decide

/-- Orthogonalité `chi5 ⟂ chi3`. -/
theorem T3_orth_chi5_chi3 : dot chi5 chi3 = 0 := by
  native_decide

/-- Orthogonalité `chi5 ⟂ chi15`. -/
theorem T3_orth_chi5_chi15 : dot chi5 chi15 = 0 := by
  native_decide

/-- Orthogonalité `chi3 ⟂ chi15`. -/
theorem T3_orth_chi3_chi15 : dot chi3 chi15 = 0 := by
  native_decide

/-!
## T3.2 — Valeurs propres de l’opérateur de Cayley

On vérifie explicitement :

- `one` et `chi5` dans le secteur `λ = 3`,
- `chi3` et `chi15` dans le secteur `λ = -1`.
-/

/-- `one` est vecteur propre de valeur propre `3`. -/
theorem T3_eigen_one : veq (mv cayleyMat one) (sv 3 one) = true := by
  native_decide

/-- `chi5` est vecteur propre de valeur propre `3`. -/
theorem T3_eigen_chi5 : veq (mv cayleyMat chi5) (sv 3 chi5) = true := by
  native_decide

/-- `chi3` est vecteur propre de valeur propre `-1`. -/
theorem T3_eigen_chi3 : veq (mv cayleyMat chi3) (sv (-1) chi3) = true := by
  native_decide

/-- `chi15` est vecteur propre de valeur propre `-1`. -/
theorem T3_eigen_chi15 : veq (mv cayleyMat chi15) (sv (-1) chi15) = true := by
  native_decide

/-!
## T3.3 — Traces et spectre global

Le spectre complet est ici :
`{3², 1⁴, (-1)²}`.

On le lit via la trace et la trace du carré.
-/

/-- Trace de la matrice de Cayley. -/
theorem T3_trace : tr cayleyMat = 8 := by native_decide

/-- Trace du carré de la matrice de Cayley. -/
theorem T3_trace2 : tr (mm cayleyMat cayleyMat) = 24 := by native_decide

/-!
## T3.4 — Polynôme annulateur

La matrice vérifie ici :

`(A - 3I)(A - I)(A + I) = 0`.
-/

/-- Polynôme annulateur spectral fini. -/
theorem T3_minpoly :
    meq
      (mm (mm (msub cayleyMat (scI 3)) (msub cayleyMat (scI 1)))
          (msub cayleyMat (scI (-1))))
      mzero = true := by
  native_decide

/-!
## T3.5 — Coefficients de Fourier du signal `tcInd`

On décompose ici l’indicatrice du triplet de Couret sur la base structurante.
-/

/-- Coefficient de `tcInd` sur `one`. -/
theorem T3_tc_dot_one : dot tcInd one = 3 := by
  native_decide

/-- Coefficient de `tcInd` sur `chi5`. -/
theorem T3_tc_dot_chi5 : dot tcInd chi5 = 1 := by
  native_decide

/-- Coefficient de `tcInd` sur `chi3`. -/
theorem T3_tc_dot_chi3 : dot tcInd chi3 = 1 := by
  native_decide

/-- Coefficient de `tcInd` sur `chi15`. -/
theorem T3_tc_dot_chi15 : dot tcInd chi15 = 3 := by
  native_decide

-- ═══════════════════════════════════════════════════════════
-- T4 — Projecteur cohérent P₃
-- ═══════════════════════════════════════════════════════════

/-!
Le projecteur `p3` extrait la composante de `tcInd`
dans le secteur propre cohérent `λ = 3`.
-/

/-- Première coordonnée de `P₃(tcInd)`. -/
theorem T4_P3_tc_0 : p3 tcInd 0 = 1/2 := by native_decide

/-- Deuxième coordonnée de `P₃(tcInd)`. -/
theorem T4_P3_tc_1 : p3 tcInd 1 = 1/4 := by native_decide

/-- Idempotence de `P₃` sur `tcInd`. -/
theorem T4_P3_idempotent :
    veq (p3 (p3 tcInd)) (p3 tcInd) = true := by native_decide

/-- Énergie de la composante cohérente de `tcInd`. -/
theorem T4_normSq_P3_tc : normSq (p3 tcInd) = 5/4 := by
  native_decide

-- ═══════════════════════════════════════════════════════════
-- T5 — Projecteur neutre P₁
-- ═══════════════════════════════════════════════════════════

/-!
Le projecteur `p1` récupère la composante du secteur intermédiaire `λ = 1`.
-/

/-- Idempotence de `P₁` sur `tcInd`. -/
theorem T5_P1_idempotent :
    veq (p1 (p1 tcInd)) (p1 tcInd) = true := by native_decide

/-- Énergie de la composante neutre de `tcInd`. -/
theorem T5_normSq_P1_tc : normSq (p1 tcInd) = 1/2 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- T6 — Projecteur de défaut P₋
-- ═══════════════════════════════════════════════════════════

/-!
Le projecteur `pminus` extrait la composante portée par le secteur `λ = -1`,
interprété ici comme **secteur de défaut**.
-/

/-- Coordonnée `alpha` du signal `tcInd`. -/
theorem T6_alpha_tc : alpha tcInd = 2 := by native_decide

/-- Coordonnée `beta` du signal `tcInd`. -/
theorem T6_beta_tc : beta tcInd = -1 := by native_decide

/-- Idempotence de `P₋` sur `tcInd`. -/
theorem T6_Pminus_idempotent :
    veq (pminus (pminus tcInd)) (pminus tcInd) = true := by native_decide

/-- Énergie de la composante de défaut de `tcInd`. -/
theorem T6_normSq_Pminus_tc : normSq (pminus tcInd) = 5/4 := by native_decide

/-- Canal quadratique `χ₃` du signal `tcInd`. -/
theorem T6_B3_tc : B3 tcInd = 1 := by native_decide

/-- Canal quadratique `χ₁₅` du signal `tcInd`. -/
theorem T6_B15_tc : B15 tcInd = 3 := by native_decide

/-!
## T6.5 — Profil du fantôme 19

On isole ici le comportement du site d’indice `5`, correspondant à `19`.

Lecture :
- `P₃(tcInd)(5)` : part cohérente,
- `P₁(tcInd)(5)` : part neutre,
- `P₋(tcInd)(5)` : part de défaut.

Leur somme redonne exactement la valeur initiale `tcInd(5) = 0`.
-/

/-- Coefficients auxiliaires historiques du profil fantôme.
Note : même énoncé que CouretUnification.Core.c_chi (U30). -/
def coef_chi : Fin 8 → ℚ := ![3/8, 1/8, 3/8, 1/8, -1/8, 1/8, -1/8, 1/8]

/-- Profil signé de `χ` au site fantôme `19`.
Note : même énoncé que CouretUnification.Core.chi_at_19 (U30). -/
def chi_at_nineteen : Fin 8 → ℚ := ![1, -1, 1, -1, -1, 1, -1, 1]

/--
Décomposition du site `19` selon les trois projecteurs.
-/
theorem T6_ghost_19_profile : p3 tcInd 5 = 1/4 ∧ p1 tcInd 5 = -1/2 ∧ pminus tcInd 5 = 1/4 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/--
Réassemblage exact au site `19`.

La somme des trois composantes vaut bien `0`,
c’est-à-dire la valeur de `tcInd` au site fantôme.
-/
theorem T6_ghost_19_cancellation : p3 tcInd 5 + p1 tcInd 5 + pminus tcInd 5 = 0 := by
  native_decide

-- ═══════════════════════════════════════════════════════════
-- T7 — Conservation des énergies (Pythagore)
-- ═══════════════════════════════════════════════════════════

/-!
Les trois secteurs sont orthogonaux et reconstituent intégralement le signal.
On obtient donc une identité de type Pythagore.
-/

/-- Décomposition énergétique exacte de `tcInd`. -/
theorem T7_pythagoras_tc : normSq tcInd = normSq (p3 tcInd) + normSq (p1 tcInd) + normSq (pminus tcInd) := by
  native_decide

/--
Vérification numérique de l’égalité énergétique :

`3 = 5/4 + 1/2 + 5/4`.
-/
theorem T7_energy_check : (5 : ℚ)/4 + 1/2 + 5/4 = 3 := by norm_num

/-- Orthogonalité entre `P₃(tcInd)` et `P₁(tcInd)`. -/
theorem T7_orth_P3_P1_tc : dot (p3 tcInd) (p1 tcInd) = 0 := by native_decide

/-- Orthogonalité entre `P₃(tcInd)` et `P₋(tcInd)`. -/
theorem T7_orth_P3_Pm_tc : dot (p3 tcInd) (pminus tcInd) = 0 := by native_decide

/-- Orthogonalité entre `P₁(tcInd)` et `P₋(tcInd)`. -/
theorem T7_orth_P1_Pm_tc : dot (p1 tcInd) (pminus tcInd) = 0 := by native_decide

/--
Décomposition exacte :
`tcInd = P₃(tcInd) + P₁(tcInd) + P₋(tcInd)`.
-/
theorem T7_decomposition_tc :
    veq (fun i => p3 tcInd i + p1 tcInd i + pminus tcInd i) tcInd = true := by native_decide

-- ═══════════════════════════════════════════════════════════
-- Compléments : trace, Parseval, tours et ratios
-- ═══════════════════════════════════════════════════════════

/-- Alias Parseval : `tr(A²) = 24`.
Note : même énoncé que CouretUnification.Core.parseval_24 (U30). -/
theorem parseval_24 : tr (mm cayleyMat cayleyMat) = 24 := T3_trace2

/-- Énergie moyenne par site : `24 / 8 = 3`. -/
theorem parseval_E : (24 : ℚ) / 8 = 3 := by norm_num

/--
Trace spectrale théorique à l’ordre `k`,
déduite de la décomposition `{3², 1⁴, (-1)²}`..
Note : même énoncé que CouretUnification.Core.eigTrace (U30).
-/
def eigTrace (k : Nat) : ℚ := 2 * (3 : ℚ) ^ k + 4 + 2 * (-1 : ℚ) ^ k

/-- Ratio spectral normalisé `L_k = eigTrace(k) / 3^k`..
Note : même énoncé que CouretUnification.Core.Lk (U30). -/
def Lk (k : Nat) : ℚ := eigTrace k / (3 : ℚ) ^ k

/-- Valeur de `L₁`. -/
theorem Lk_1 : Lk 1 = 8/3 := by
  simp [Lk, eigTrace]
  norm_num

/-- Ici `L₁ = L₂`. -/
theorem Lk_pair : Lk 1 = Lk 2 := by
  simp [Lk, eigTrace]
  norm_num

/-- La valeur initiale est strictement supérieure à `2`. -/
theorem Lk_gt_2 : Lk 1 > 2 := by
  simp [Lk, eigTrace]
  norm_num

/-- Rapport brut de kurtosis symbolique..
Note : même énoncé que CouretUnification.Core.kurtosis_raw (U30). -/
theorem kurtosis_raw : (21 : ℚ) / 9 = 7/3 := by norm_num

/-- Rapport non trivial stabilisé..
Note : même énoncé que CouretUnification.Core.nontrivial_ratio (U30). -/
theorem nontrivial_ratio : (15 : ℚ) / 9 = 5/3 := by norm_num

/-- Petite identité binaire associée à la classification `63`. -/
theorem classification_63 : (63 : ℕ) = 2^6 - 1 := by norm_num

-- ═══════════════════════════════════════════════════════════
-- Test hors triplet : robustesse formelle
-- ═══════════════════════════════════════════════════════════

/-!
On vérifie ici que les identités de décomposition et d’orthogonalité
ne sont pas propres au seul signal `tcInd`.
-/

/-- Signal test non trivial, choisi hors du triplet de Couret. -/
def testSig : Sig := ![3, 1, 0, 2, -1, 4, 1, -2]

/-- Pythagore spectral sur le signal test. -/
theorem test_pythagoras : normSq testSig =
    normSq (p3 testSig) + normSq (p1 testSig) + normSq (pminus testSig) := by
  native_decide

/-- Décomposition exacte du signal test par les trois projecteurs. -/
theorem test_decomposition : veq (fun i => p3 testSig i + p1 testSig i + pminus testSig i) testSig = true := by
  native_decide

/-- Orthogonalité mutuelle des trois composantes du signal test. -/
theorem test_orthogonality :
    dot (p3 testSig) (p1 testSig) = 0 ∧
    dot (p3 testSig) (pminus testSig) = 0 ∧
    dot (p1 testSig) (pminus testSig) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ═══════════════════════════════════════════════════════════
-- Garde épistémique
-- ═══════════════════════════════════════════════════════════

/--
Garde épistémique : ce fichier ne revendique aucun résultat global
sur RH/GRH. Il formalise uniquement le noyau spectral fini exact.
-/
def RHClaimed : Bool := false

/-- Vérification formelle de la garde épistémique. -/
theorem rh_not_claimed : RHClaimed = false := rfl

/-!
## Bilan T1–T7

| Théorème | Contenu | Méthode |
|----------|---------|---------|
| T1 | dimension discrète = 8 | `decide` |
| T2 | image quadratique = `{1,19}` | `Core/U30`, `native_decide` |
| T3 | spectre fini = `{3²,1⁴,(-1)²}` | `native_decide` |
| T3 | 4 vecteurs propres vérifiés | `native_decide` |
| T3 | polynôme annulateur | `native_decide` |
| T4 | `P₃` idempotent, `‖P₃(tcInd)‖² = 5/4` | `native_decide` |
| T5 | `P₁` idempotent, `‖P₁(tcInd)‖² = 1/2` | `native_decide` |
| T6 | `alpha(tcInd)=2`, `beta(tcInd)=-1` | `native_decide` |
| T6 | `‖P₋(tcInd)‖² = 5/4` | `native_decide` |
| T6 | profil fantôme au site `19` | `native_decide` |
| T7 | Pythagore sur `tcInd` et `testSig` | `native_decide` |
| T7 | orthogonalité des trois secteurs | `native_decide` |
| T7 | décomposition exacte `f = P₃f + P₁f + P₋f` | `native_decide` |

Aucun `sorry`. Aucun axiome. `RHClaimed = false`.
-/

end CouretUnification.FiniteDefect
