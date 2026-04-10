import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.Linarith

namespace CouretUnification.Analytic.VerifiedIntervals

/-!
# VerifiedIntervals.lean
## Arithmétique d'intervalles certifiée, couche générique

Cette brique Lean formalise une arithmétique d'intervalles minimale
mais suffisante pour un usage de validation numérique certifiée.

Philosophie InterIA :
- on garde ici une couche **froide, propre, générique** ;
- aucun axiome métier ne vit dans ce fichier ;
- les hypothèses spécifiques (signal spectral, gap, etc.) sont injectées
  dans les fichiers d'instanciation, jamais dans le cœur générique ;
- le rôle de cette couche est de transformer un certificat rationnel
  en inégalité Lean exploitable sans `sorry`.

Pipeline conceptuel :
`Python / calcul externe` → `bornes rationnelles` → `Lean` → `théorème exact`.

Statut épistémique :
- `0 sorry`
- `0 axiome`
- `RHClaimed = false`

Autrement dit : ici, on ne "raconte" rien ; on **verrouille**.
-/

-- ═══════════════════════════════════════════════════════════
-- §1. INTERVALLE CERTIFIÉ
-- ═══════════════════════════════════════════════════════════

/-- Un intervalle rationnel certifié `[lo, hi]` avec preuve interne
que la borne inférieure ne dépasse pas la borne supérieure. -/
structure CertifiedInterval where
  lo : ℚ
  hi : ℚ
  hle : lo ≤ hi

namespace CertifiedInterval

/-- `I.contains x` signifie que le réel `x` appartient à l'intervalle
certifié `I`. On caste simplement les bornes rationnelles en réels. -/
def contains (I : CertifiedInterval) (x : ℝ) : Prop :=
  ((I.lo : ℝ) ≤ x) ∧ (x ≤ (I.hi : ℝ))

/-- `I.containsZero` signifie que `0` appartient à l'intervalle. -/
def containsZero (I : CertifiedInterval) : Prop :=
  I.contains 0

/-- Largeur réelle de l'intervalle.
Comme `lo ≤ hi`, cette quantité est toujours non négative. -/
def width (I : CertifiedInterval) : ℝ :=
  ((I.hi - I.lo : ℚ) : ℝ)

end CertifiedInterval

-- ═══════════════════════════════════════════════════════════
-- §2. LEMMES GÉOMÉTRIQUES DE BASE
-- ═══════════════════════════════════════════════════════════

/-- La largeur d'un intervalle certifié est non négative.
C'est le premier garde-fou géométrique du fichier. -/
lemma width_nonneg (I : CertifiedInterval) : 0 ≤ I.width := by
  dsimp [CertifiedInterval.width]
  exact_mod_cast sub_nonneg.mpr I.hle

/-- Passage technique : la largeur rationnelle castée dans `ℝ`
coïncide avec la différence réelle des bornes castées.

Ce lemme isole un petit détail de coercions pour garder les preuves
principales lisibles. -/
lemma width_cast (I : CertifiedInterval) :
    (((I.hi - I.lo) : ℚ) : ℝ) = (I.hi : ℝ) - (I.lo : ℝ) := by
  push_cast
  rfl

/-- **Lemme central de géométrie d'intervalle**

Si `x` est contenu dans `[lo, hi]` et si `0` appartient aussi à cet intervalle,
alors `|x|` est majoré par la largeur de l'intervalle.

Lecture InterIA :
si le signal et zéro vivent dans la même cage certifiée,
alors l'amplitude absolue du signal ne peut pas dépasser l'ouverture de la cage.
-/
lemma abs_le_width_of_contains_and_zero
    (I : CertifiedInterval) {x : ℝ}
    (hx : I.contains x) (hz : I.containsZero) :
    |x| ≤ I.width := by
  rcases hx with ⟨hlo, hhi⟩
  rcases hz with ⟨hzlo, hzhi⟩
  dsimp [CertifiedInterval.width]
  rw [width_cast]
  apply abs_le.mpr
  constructor <;> linarith

-- ═══════════════════════════════════════════════════════════
-- §3. ISOLEMENT SPECTRAL ABSTRAIT
-- ═══════════════════════════════════════════════════════════

/-- Structure abstraite d'un signal spectral isolé.

On encode :
- une valeur `signal`,
- un `gap` strictement positif,
- une propriété d'isolement : si le signal n'est pas nul,
  alors sa valeur absolue est au moins égale au gap.

Cette structure reste volontairement générique :
elle ne suppose aucune origine analytique particulière du signal. -/
structure SpectralIsolation where
  signal : ℝ
  gap : ℝ
  gap_pos : 0 < gap
  isolated : signal ≠ 0 → gap ≤ |signal|

-- ═══════════════════════════════════════════════════════════
-- §4. THÉORÈME DE NULLITÉ CERTIFIÉE
-- ═══════════════════════════════════════════════════════════

/-- **Théorème de nullité par intervalle certifié**

Si :
1. le signal appartient à un intervalle certifié `I`,
2. `0` appartient aussi à `I`,
3. la largeur de `I` est strictement plus petite que le gap spectral,

alors le signal est nécessairement nul.

Lecture InterIA :
- l'isolement spectral dit qu'un signal non nul doit rester à distance
  au moins `gap` de l'origine ;
- le certificat intervallaire dit au contraire que le signal est enfermé
  dans une zone contenant `0` et de largeur trop petite ;
- les deux informations sont incompatibles, donc le signal vaut `0`.
-/
theorem exact_zero_of_certified_interval
    (S : SpectralIsolation)
    (I : CertifiedInterval)
    (hcontain : I.contains S.signal)
    (hzero : I.containsZero)
    (hwidth : I.width < S.gap) :
    S.signal = 0 := by
  by_contra hne
  have hgap : S.gap ≤ |S.signal| := S.isolated hne
  have hspan : |S.signal| ≤ I.width :=
    abs_le_width_of_contains_and_zero I hcontain hzero
  exact (not_le_of_gt hwidth) (le_trans hgap hspan)

-- ═══════════════════════════════════════════════════════════
-- §5. GARDE-FOU ÉPISTÉMIQUE
-- ═══════════════════════════════════════════════════════════

/-- Drapeau explicite : ce fichier ne revendique rien sur RH. -/
def RHClaimed : Bool := false

/-- Vérification triviale du garde-fou épistémique. -/
theorem rh_not_claimed : RHClaimed = false := rfl

end CouretUnification.Analytic.VerifiedIntervals