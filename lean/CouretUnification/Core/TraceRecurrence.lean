import CouretUnification.Core.FormuleLk
import Mathlib.Tactic

namespace CouretUnification.Core.TraceRecurrence

/-!
# Récurrence des traces spectrales

Le polynôme minimal (X−3)(X−1)(X+1) = X³ − 3X² − X + 3
donne la récurrence sur les sommes de puissances :
  s_k = 3·s_{k−1} + s_{k−2} − 3·s_{k−3}   pour tout k ≥ 3
-/

open FormuleLk

-- ═══════════════════════════════════════════
-- Récurrence entière des traces vérifiée pour k = 3..10
-- ═══════════════════════════════════════════

theorem init_0 : eigTrace 0 = 8 := by norm_num [eigTrace]
theorem init_1 : eigTrace 1 = 8 := by norm_num [eigTrace]
theorem init_2 : eigTrace 2 = 24 := by norm_num [eigTrace]

theorem rec_3 : eigTrace 3 = 3 * eigTrace 2 + eigTrace 1 - 3 * eigTrace 0 := by
  norm_num [eigTrace]
theorem rec_4 : eigTrace 4 = 3 * eigTrace 3 + eigTrace 2 - 3 * eigTrace 1 := by
  norm_num [eigTrace]
theorem rec_5 : eigTrace 5 = 3 * eigTrace 4 + eigTrace 3 - 3 * eigTrace 2 := by
  norm_num [eigTrace]
theorem rec_6 : eigTrace 6 = 3 * eigTrace 5 + eigTrace 4 - 3 * eigTrace 3 := by
  norm_num [eigTrace]
theorem rec_7 : eigTrace 7 = 3 * eigTrace 6 + eigTrace 5 - 3 * eigTrace 4 := by
  norm_num [eigTrace]
theorem rec_8 : eigTrace 8 = 3 * eigTrace 7 + eigTrace 6 - 3 * eigTrace 5 := by
  norm_num [eigTrace]
theorem rec_9 : eigTrace 9 = 3 * eigTrace 8 + eigTrace 7 - 3 * eigTrace 6 := by
  norm_num [eigTrace]
theorem rec_10 : eigTrace 10 = 3 * eigTrace 9 + eigTrace 8 - 3 * eigTrace 7 := by
  norm_num [eigTrace]

-- ═══════════════════════════════════════════
-- Récurrence rationnelle : L_k = L_{k−1} + L_{k−2}/9 − L_{k−3}/9
-- ═══════════════════════════════════════════

theorem Lk_rec_3 : Lk 3 = Lk 2 + Lk 1 / 9 - Lk 0 / 9 := by
  simp [Lk, eigTrace]; norm_num
theorem Lk_rec_4 : Lk 4 = Lk 3 + Lk 2 / 9 - Lk 1 / 9 := by
  simp [Lk, eigTrace]; norm_num
theorem Lk_rec_5 : Lk 5 = Lk 4 + Lk 3 / 9 - Lk 2 / 9 := by
  simp [Lk, eigTrace]; norm_num
theorem Lk_rec_6 : Lk 6 = Lk 5 + Lk 4 / 9 - Lk 3 / 9 := by
  simp [Lk, eigTrace]; norm_num

-- ═══════════════════════════════════════════
-- Polynôme minimal
-- ═══════════════════════════════════════════

theorem minpoly_expand (x : Int) :
    (x - 3) * (x - 1) * (x + 1) = x ^ 3 - 3 * x ^ 2 - x + 3 := by ring

theorem root_3 : (3 : Int) ^ 3 - 3 * 3 ^ 2 - 3 + 3 = 0 := by norm_num
theorem root_1 : (1 : Int) ^ 3 - 3 * 1 ^ 2 - 1 + 3 = 0 := by norm_num
theorem root_m1 : (-1 : Int) ^ 3 - 3 * (-1) ^ 2 - (-1) + 3 = 0 := by norm_num

-- ═══════════════════════════════════════════
-- Récurrence universelle pour chaque valeur propre
-- ═══════════════════════════════════════════

/-- Pour toute racine r de X³ = 3X² + X − 3 :
    r^k = 3·r^{k−1} + r^{k−2} − 3·r^{k−3} pour k ≥ 3.

    Preuve : r^k = r^{k−3} · r³ = r^{k−3} · (3r² + r − 3). -/
theorem root_recurrence (r : Int) (k : Nat) (hk : k ≥ 3)
    (hroot : r ^ 3 = 3 * r ^ 2 + r - 3) :
    r ^ k = 3 * r ^ (k - 1) + r ^ (k - 2) - 3 * r ^ (k - 3) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  have e1 : n + 3 - 1 = n + 2 := by omega
  have e2 : n + 3 - 2 = n + 1 := by omega
  have e3 : n + 3 - 3 = n := by omega
  rw [e1, e2, e3, pow_add r n 3, pow_add r n 2, pow_add r n 1, hroot]
  ring

theorem hroot_3 : (3 : Int) ^ 3 = 3 * 3 ^ 2 + 3 - 3 := by norm_num
theorem hroot_1 : (1 : Int) ^ 3 = 3 * 1 ^ 2 + 1 - 3 := by norm_num
theorem hroot_m1 : (-1 : Int) ^ 3 = 3 * (-1) ^ 2 + (-1) - 3 := by norm_num

/-!
## Synthèse

**Récurrence** : s_k = 3·s_{k−1} + s_{k−2} − 3·s_{k−3}
- Initialisation : s₀ = 8, s₁ = 8, s₂ = 24
- Vérifiée pour k = 3..10 par `norm_num`
- Preuve universelle : `root_recurrence` (`pow_add` + `ring`)

**Source** : polynôme minimal (X−3)(X−1)(X+1) = X³ − 3X² − X + 3
-/

end CouretUnification.Core.TraceRecurrence
