import Lake
open Lake DSL

package «CouretUnification» where
  -- Options Lean 4 pour le projet
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.29.1"

@[default_target]
lean_lib «CouretUnification» where
  srcDir := "lean"
  -- Tous les fichiers sous lean/CouretUnification/ sont inclus
  roots := #[`CouretUnification]
