/-
# ResGold.lean

Fichier-racine du module `ResGold` (sous-programme du programme
Couret–Unification, dossier Expert / ResGold local).

Importe les couches L0, L1, L2 et vérifie l'invariant de compilation `RHClaimed = false`.

## Architecture

```
ResGold.lean                        -- ce fichier
├── ResGold/Status.lean             -- statuts épistémiques + RHClaimed
├── ResGold/L0_LocalLemma.lean      -- AdelicLocalLemma : I_p(R) = ν_p(R)/(p−1)
├── ResGold/L1_ConductorOne.lean    -- opérateur conducteur 1, spectre, HS, trace
└── ResGold/L2_MertensAsymptotic.lean -- mertensA_P(R) = log log P + B_R + o(1) (paramétré)
```

## Doctrine

Aucun fichier de cette hiérarchie n'introduit `axiom`. Les énoncés
non démontrés utilisent `sorry`, traçable et local.

L'identification globale `det₂(I − zM) ∼ ξ(½ + iz)` n'est **pas**
formulée dans ce module. Elle relève de modules `VerrouA.lean`,
`VerrouF.lean` à créer ultérieurement après validation L0–L2.

## v38.5 — État après corrections

* Bug `True` placeholders éliminé : `signedTrace_spec` et
  `psi_L2_eq_HSnorm` portent désormais des énoncés substantiels.
* Constante de Mertens paramétrée : `mertensA_asymptotic_param` prend
  l'asymptotique de Mertens en hypothèse, suivant le pattern `L7For`
  v38.3. Aucun `sorry` au niveau d'une constante.
* Import inutile `Mathlib.NumberTheory.Padics.PadicNumbers` retiré de L2.

Voir `RESGOLD_CORRECTIONS_v38.5_NOTE.md` pour le détail des corrections.

## État de compilation attendu (validé par Thomas)

* Compile sans erreur
* Sorries présents documentés par bloc `[D, provable]` ou `[H]` ou `[O]`
* Aucun axiome
* `#print axioms CouretUnification.ResGold.rh_not_claimed` doit retourner
  `does not depend on any axioms`. (voir Audit.PrintAxioms)

Auteur : programme Couret–Unification.
Squelette validé et dédupliqué par Thomas (Lean 4 / Mathlib v4.29.1).
-/

import CouretUnification.ResGold.Status
import CouretUnification.ResGold.L0_LocalLemma
import CouretUnification.ResGold.L1_ConductorOne
import CouretUnification.ResGold.L2_MertensAsymptotic

namespace CouretUnification.ResGold

/-- Vérification triviale : RHClaimed est false par construction. -/
theorem ResGold_module_does_not_claim_RH : RHClaimed = false := rfl

/-- Statut consolidé des objets de ce module, à des fins documentaires.

Mis à jour v38.5 : les entrées Mertens et signedTrace reflètent la
correction (paramétrisation et énoncés substantiels). -/
def statusTable : List (String × ResGoldStatus) :=
  [ ("nu_value (combinatorial)",               ResGoldStatus.D)
  , ("Jcal_one, Jcal_nontrivial",              ResGoldStatus.D)
  , ("Ip_quotient (rational form)",            ResGoldStatus.D)
  , ("I_p(R) as p-adic integral",              ResGoldStatus.H)
  , ("M^(1,0) conductorOneEigenvalue_abs_sq",  ResGoldStatus.D)
  , ("HSnorm_sq_eq (definition)",              ResGoldStatus.D)
  , ("signedTrace_three_cases",                ResGoldStatus.D)  -- v38.5: replaces True
  , ("signedTrace ↔ spectral sum",             ResGoldStatus.O)  -- v38.5: requires Fintype
  , ("psi_L2_eq_HSnorm (real identity)",       ResGoldStatus.D)  -- v38.5: replaces True
  , ("mertensA_P(R) truncated sum",            ResGoldStatus.D)
  , ("Dconst (convergent series)",             ResGoldStatus.D)
  , ("Bconst_param (Mertens-parametric)",      ResGoldStatus.D)  -- v38.5: parametric form
  , ("mertensA_asymptotic_param",              ResGoldStatus.D)  -- v38.5: conditional on h_mertens
  , ("MertensConstant (external)",             ResGoldStatus.H)  -- v38.5: out of module
  , ("global renormalized tensor",             ResGoldStatus.H)
  , ("Poisson compatibility (Gate 0)",         ResGoldStatus.O)
  , ("det₂(I − zM) ∼ ξ(½ + iz)",               ResGoldStatus.O)
  ]

end CouretUnification.ResGold
