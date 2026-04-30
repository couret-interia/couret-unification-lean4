/-
  Couret-Unification — v35.9.0
  Logic/ExplicitFormula/PrimeSide.lean

  Objet : LE CÔTÉ ARITHMÉTIQUE DE LA FORMULE EXPLICITE.

         Contient la PREMIÈRE FERMETURE MATHÉMATIQUE du programme
         dans le pont Riemann-Weil :

             supp(g) ⊂ [-A, A]  ⇒  ∃ N, ∀ n > N, primeTerm(n) = 0.

         C'est la compression FCI appliquée à la formule explicite :
         l'infini arithmétique est ramené au fini par le support compact.

         Importance stratégique : ce théorème est la première pierre
         véritablement prouvée (pas simplement une structure typée) du
         pont. Il transforme le `tsum` infini en `Finset.sum` fini, sans
         invoquer aucune propriété profonde de la fonction de von Mangoldt.

  Statut     : Frozen-eligible (0 sorry, 0 axiome local, théorèmes prouvés)
  Layer      : Logic.ExplicitFormula
  Dépend de  : Logic.ExplicitFormula.TestFunctions
               Logic.ExplicitFormula.ArithmeticWeight
               Mathlib.Analysis.SpecialFunctions.Log.Basic
               Mathlib.Analysis.SpecialFunctions.Exp
  Doctrine   : Aucune propriété de Λ(n) n'est invoquée. Le théorème
               fonctionne pour TOUT ArithmeticWeight.
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0

  Changements v35.9-pre → v35.9.0 :
    (1) Poids abstrait `ArithmeticWeight` au lieu de `vonMangoldt` opaque.
    (2) Seuil N choisi via `exists_nat_gt (Real.exp A)`, pas via
        `Nat.floor (Real.exp A)` — évite le piège `N < n ⇏ exp A < n`.
    (3) Passage à ℝ/ℂ réels via Mathlib.

  Pour Bernard.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import CouretUnification.Logic.ExplicitFormula.TestFunctions
import CouretUnification.Logic.ExplicitFormula.ArithmeticWeight

namespace CouretUnification.Logic.ExplicitFormula

/- ═══════════════════════════════════════════════════════════════════════════
   LE TERME PRIMAIRE
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Le terme arithmétique à l'indice n dans la formule explicite.

    Forme canonique sous convention negativeExp :

        primeTerm(n) = Λ(n) · (g(log n) + g(-log n))

    (le facteur 1/√n et le signe global sont absorbés dans l'objet trace
    final ; voir ExplicitFormulaBridge). -/
noncomputable def primeTerm
    (Λ : ArithmeticWeight) (φ : TestPairBasic) (n : ℕ) : ℂ :=
  (Λ.weight n : ℂ) *
    (φ.g (Real.log (n : ℝ)) + φ.g (-Real.log (n : ℝ)))

/- ═══════════════════════════════════════════════════════════════════════════
   THÉORÈME DE COMPRESSION (pointwise)
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Si log n dépasse le rayon A du support de g, alors le terme primaire
    s'annule exactement, quel que soit le poids arithmétique choisi. -/
theorem primeTerm_zero_of_log_gt_support
    (Λ : ArithmeticWeight)
    (φ : TestPairBasic)
    (A : ℝ)
    (hApos : 0 < A)
    (hSupp : ∀ x : ℝ, A < |x| → φ.g x = 0)
    (n : ℕ)
    (hlog : A < Real.log (n : ℝ)) :
    primeTerm Λ φ n = 0 := by
  -- Étape 1 : log n > 0 puisque log n > A > 0.
  have hlog_pos : 0 < Real.log (n : ℝ) := lt_trans hApos hlog
  -- Étape 2 : |log n| > A.
  have h_abs_log : A < |Real.log (n : ℝ)| := by
    rw [abs_of_nonneg (le_of_lt hlog_pos)]
    exact hlog
  -- Étape 3 : |-log n| > A.
  have h_abs_neg_log : A < |-(Real.log (n : ℝ))| := by
    rw [abs_neg, abs_of_nonneg (le_of_lt hlog_pos)]
    exact hlog
  -- Étape 4 : application du support compact dans les deux directions.
  have h1 : φ.g (Real.log (n : ℝ)) = 0 :=
    hSupp (Real.log (n : ℝ)) h_abs_log
  have h2 : φ.g (-(Real.log (n : ℝ))) = 0 :=
    hSupp (-(Real.log (n : ℝ))) h_abs_neg_log
  -- Étape 5 : le terme entier s'annule.
  simp [primeTerm, h1, h2]

/- ═══════════════════════════════════════════════════════════════════════════
   THÉORÈME DE FINITUDE (PREMIÈRE FERMETURE MATHÉMATIQUE)
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- THÉORÈME CENTRAL : sous support compact, le PrimeSide est fini.

    Plus précisément, il existe un seuil N tel que tous les termes
    arithmétiques d'indice n > N s'annulent.

    C'est la compression FCI appliquée à la formule explicite :
        PrimeSide tsum (infini)  →  Finset.sum sur {n ≤ N} (fini).

    Preuve : on choisit N > exp(A) via l'archimédianité de ℕ dans ℝ
    (`exists_nat_gt`), puis on applique le lemme ponctuel.

    Note sur le seuil : en v35.9-pre, on avait `N := ⌊exp A⌋₊`. C'était
    un bug subtil car `N < n` avec `N = ⌊exp A⌋` ne garantit pas
    `exp A < n` (cas limite quand exp A est entier). En v35.9.0, on
    utilise `exists_nat_gt` qui assure strictement `exp A < N`. -/
theorem primeSide_finite_of_compactSupport
    (Λ : ArithmeticWeight)
    (φ : TestPairBasic) :
    ∃ N : ℕ, ∀ n : ℕ, N < n → primeTerm Λ φ n = 0 := by
  -- Extraction du rayon du support compact.
  rcases φ.compactSupport_g with ⟨A, hApos, hSupp⟩
  -- Choix robuste du seuil : on prend N strictement supérieur à exp A.
  -- Ici, `exists_nat_gt` fournit un entier N avec `Real.exp A < N`.
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp A)
  refine ⟨N, ?_⟩
  intro n hn
  -- Cast du passage N < n (en ℕ) vers (N : ℝ) < (n : ℝ).
  have hn_real : (N : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- Transitivité : exp A < N ≤ n.
  have hexp_lt_n : Real.exp A < (n : ℝ) := lt_trans hN hn_real
  -- n > 0 car exp A > 0 et exp A < n.
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans (Real.exp_pos A) hexp_lt_n
  -- Passage au log : exp A < n ⇔ A < log n (pour n > 0).
  have hlog : A < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt hn_pos).2 hexp_lt_n
  -- Application du lemme ponctuel.
  exact primeTerm_zero_of_log_gt_support Λ φ A hApos hSupp n hlog

/- ═══════════════════════════════════════════════════════════════════════════
   STRUCTURE PrimeSide (DÉFINITION OPÉRATIONNELLE)
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Certificat de finitude du support du PrimeSide, instanciable par
    le théorème ci-dessus. -/
structure PrimeSideFiniteSupport
    (Λ : ArithmeticWeight) (φ : TestPairBasic) where
  cutoff          : ℕ
  vanishesBeyond  : ∀ n : ℕ, cutoff < n → primeTerm Λ φ n = 0

/-- Construction canonique du certificat de finitude via le théorème
    central `primeSide_finite_of_compactSupport`. -/
noncomputable def buildPrimeSideFiniteSupport
    (Λ : ArithmeticWeight) (φ : TestPairBasic) :
    PrimeSideFiniteSupport Λ φ :=
  let ⟨N, hN⟩ := primeSide_finite_of_compactSupport Λ φ
  { cutoff := N, vanishesBeyond := hN }

/-- Le côté arithmétique comme objet structural (placeholder pour une
    somme finie explicite — la définition concrète comme `Finset.sum`
    sur `Finset.Icc 1 cutoff` appartient aux modules de calcul). -/
structure PrimeSide where
  value                  : ∀ (Λ : ArithmeticWeight) (φ : TestPairBasic), ℂ
  finiteSupportCertified : ∀ (Λ : ArithmeticWeight) (φ : TestPairBasic),
                             PrimeSideFiniteSupport Λ φ

/- ═══════════════════════════════════════════════════════════════════════════
   BILAN
   ═══════════════════════════════════════════════════════════════════════════

   Ce module démontre, SANS AXIOME LOCAL et SANS PROPRIÉTÉ de vonMangoldt :

   1. primeTerm_zero_of_log_gt_support : pointwise vanishing.
   2. primeSide_finite_of_compactSupport : finite support globally.
   3. buildPrimeSideFiniteSupport : certificate construction.

   C'est la première fermeture véritable (pas juste une structure) du
   pont Riemann-Weil dans Lean 4. Le verrou résiduel se déplace alors
   entièrement sur le ZeroSide, où il sera traité par Riemann-von Mangoldt
   + Paley-Wiener + identité d'Abel (voir ZeroCounting.lean, ZeroSide.lean).
-/

end CouretUnification.Logic.ExplicitFormula
