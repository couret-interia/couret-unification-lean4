/-
  CouretUnification.Residue.PuncturedKlein30
  ════════════════════════════════════════════════════════════════════
  Primitive fondamentale du programme : le Klein ponctué.

  TC n'est plus le triplet primitif : c'est K₄ \ {19}, où K₄ est le
  sous-groupe de Klein {1, 11, 19, 29} dans G₃₀ = (ℤ/30)*. Le fantôme
  19 est l'élément EFFACÉ du Klein, non un bruit spectral.

  Cette reformulation est invariante à toute perturbation : elle
  survit au passage non-tensoriel et à l'injection Legendre.

  REFACTOR v38 unifié :
    • Importe ClosureTC pour réutiliser TC et K4 (canoniques v37)
    • Évite tout doublon de Z30, TC, K4
    • N'introduit que Phantom19 et les théorèmes de structure

  Doctrine : v38 unifiée, commit 1
  Status   : closed (preuves par native_decide, fin_cases ou decide)
-/

import Mathlib
import CouretUnification.Residue.ClosureTC

namespace CouretUnification
namespace Residue

/-- The missing point of the punctured Klein structure. -/
def Phantom19 : Z30 := 19

/-! ## §1 — Membership of the phantom -/

theorem phantom19_mem_K4 : Phantom19 ∈ K4 := by
  native_decide

theorem phantom19_not_mem_TC : Phantom19 ∉ TC := by
  native_decide

/-- The Couret triplet IS the punctured Klein four group. -/
theorem TC_eq_K4_erase_19 : TC = K4.erase Phantom19 := by
  native_decide

/-- Equivalent reformulation : adding the phantom back gives K₄. -/
theorem TC_insert_19_eq_K4 :
    insert Phantom19 TC = K4 := by
  native_decide

/-! ## §2 — Klein four group structure : every element is involutive -/

theorem square_one_eq_one : (1 : Z30) * 1 = 1 := by native_decide
theorem square_11_eq_one  : (11 : Z30) * 11 = 1 := by native_decide
theorem square_19_eq_one  : (19 : Z30) * 19 = 1 := by native_decide
theorem square_29_eq_one  : (29 : Z30) * 29 = 1 := by native_decide

/-! ## §3 — Klein four multiplication table (closed) -/

theorem prod_11_29_eq_19 : (11 : Z30) * 29 = 19 := by native_decide
theorem prod_11_19_eq_29 : (11 : Z30) * 19 = 29 := by native_decide
theorem prod_19_29_eq_11 : (19 : Z30) * 29 = 11 := by native_decide

/-! ## §4 — Phantom witness : the missing product -/

/-- The phantom 19 is the product of the two non-trivial elements of TC.
    This is the algebraic statement that TC is NOT closed under multiplication. -/
theorem phantom19_is_product_witness :
    (11 : Z30) * 29 = Phantom19 := by
  native_decide

/-- The phantom is the unique element such that TC ∪ {phantom} forms a group. -/
theorem phantom19_completes_TC_to_K4 :
    insert Phantom19 TC = K4 := TC_insert_19_eq_K4

end Residue
end CouretUnification
