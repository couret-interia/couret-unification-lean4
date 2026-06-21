/-
  CouretUnification.Residue.PuncturedKlein30
  ════════════════════════════════════════════════════════════════════
  Primitive fondamentale du programme : le Klein ponctué.

  TC n'est plus le triplet primitif : c'est K₄ \ {19}, où K₄ est le
  sous-groupe de Klein {1, 11, 19, 29} dans G₃₀ = (ℤ/30)*. Le fantôme
  19 est l'élément EFFACÉ du Klein, non un bruit spectral.

  Cette reformulation est invariante à toute perturbation : elle
  survit au passage non tensoriel et à l'injection de Legendre.

  REFACTOR v38 unifié :
    • Importe ClosureTC pour réutiliser TC et K4 — canoniques v37.
    • Évite tout doublon de Z30, TC, K4.
    • N'introduit que Phantom19 et les théorèmes de structure.

  Doctrine : v38 unifiée, commit 1.
  Statut   : fermé — preuves par native_decide, fin_cases ou decide.
-/

import CouretUnification.Residue.ClosureTC

namespace CouretUnification.Residue

/-- Le point manquant de la structure de Klein ponctuée. -/
def Phantom19 : Z30 := 19

/-! ## §1 — Appartenance du fantôme -/

theorem phantom19_mem_K4 : Phantom19 ∈ K4 := by
  native_decide

theorem phantom19_not_mem_TC : Phantom19 ∉ TC := by
  native_decide

/-- Le triplet de Couret EST le groupe de Klein à quatre éléments ponctué. -/
theorem TC_eq_K4_erase_19 : TC = K4.erase Phantom19 := by
  native_decide

/-- Reformulation équivalente : réinsérer le fantôme redonne K₄. -/
theorem TC_insert_19_eq_K4 :
    insert Phantom19 TC = K4 := by
  native_decide

/-! ## §2 — Structure du groupe de Klein : chaque élément est involutif -/

theorem square_one_eq_one : (1 : Z30) * 1 = 1 := by native_decide
theorem square_11_eq_one  : (11 : Z30) * 11 = 1 := by native_decide
theorem square_19_eq_one  : (19 : Z30) * 19 = 1 := by native_decide
theorem square_29_eq_one  : (29 : Z30) * 29 = 1 := by native_decide

/-! ## §3 — Table de multiplication du groupe de Klein — fermée -/

theorem prod_11_29_eq_19 : (11 : Z30) * 29 = 19 := by native_decide
theorem prod_11_19_eq_29 : (11 : Z30) * 19 = 29 := by native_decide
theorem prod_19_29_eq_11 : (19 : Z30) * 29 = 11 := by native_decide

/-! ## §4 — Témoin fantôme : le produit manquant -/

/-- Le fantôme 19 est le produit des deux éléments non triviaux de TC.
    C'est l'énoncé algébrique affirmant que TC n'est PAS fermé pour la
    multiplication. -/
theorem phantom19_is_product_witness :
    (11 : Z30) * 29 = Phantom19 := by
  native_decide

/-- Le fantôme est l'élément qui complète TC en un groupe lorsqu'on le
    réinsère : TC ∪ {fantôme} forme alors K₄. -/
theorem phantom19_completes_TC_to_K4 :
    insert Phantom19 TC = K4 := TC_insert_19_eq_K4

end CouretUnification.Residue
