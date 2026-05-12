-- =========================================================================
-- Couret-Unification / TowerLift v18
-- Module : Examples/ToyModelFloat.lean
--
-- Version exécutable (#eval) avec Float
-- =========================================================================

import Mathlib.Data.Nat.Prime.Defs

namespace CouretUnification.ToyModelFloat

def residues30 : Fin 8 → Nat
  | ⟨0, _⟩ => 1  | ⟨1, _⟩ => 7  | ⟨2, _⟩ => 11 | ⟨3, _⟩ => 13
  | ⟨4, _⟩ => 17 | ⟨5, _⟩ => 19 | ⟨6, _⟩ => 23 | ⟨7, _⟩ => 29

def epsilon30F (p : Nat) : Float :=
  match p % 30 with
  | 1 => 1.0 | 7 => 1.0 | 11 => -1.0 | 13 => 1.0
  | 17 => -1.0 | 19 => 1.0 | 23 => -1.0 | 29 => 1.0
  | _ => 0.0

def lambdaF : Float := 1.0 / Float.sqrt 7.0

def heckeT2 (r : Nat) : Nat := (2 * r + 1) % 30

-- Vérifications exécutables
#eval heckeT2 11   -- 23
#eval heckeT2 23   -- 17
#eval heckeT2 29   -- 29

#eval epsilon30F 11  -- -1.0
#eval epsilon30F 23  -- -1.0
#eval epsilon30F 29  --  1.0

-- Test de restriction mod 30
#eval [1,7,11,13,17,19,23,29].map (fun r => (r, heckeT2 r))
-- Seuls 11→23, 23→17, 29→29 restent dans R₃₀

-- Constantes spectrales du scan
def sgDeltaPos : Float := 0.37517432
def sgDeltaDom : Float := -0.39639813

#eval Float.abs (sgDeltaPos - lambdaF)  -- écart ≈ 0.0028
#eval Float.abs (sgDeltaPos - lambdaF) / lambdaF * 100.0  -- ≈ 0.74%

-- Chaîne de Cunningham 41 → 83 → 167
#eval Nat.Prime 41   -- true
#eval 2 * 41 + 1     -- 83
#eval Nat.Prime 83   -- true
#eval 2 * 83 + 1     -- 167
#eval Nat.Prime 167  -- true
#eval 2 * 167 + 1    -- 335
#eval Nat.Prime 335  -- false

#eval 41 % 30   -- 11
#eval 83 % 30   -- 23
#eval 167 % 30  -- 17

-- Point fixe S.29
#eval Nat.Prime 89    -- true
#eval 89 % 30         -- 29
#eval 2 * 89 + 1      -- 179
#eval Nat.Prime 179   -- true
#eval 179 % 30        -- 29

-- Matrice M₃ (comptages bruts, vérifiables)
def M3_counts : Fin 3 → Fin 3 → Nat
  | ⟨0, _⟩, ⟨0, _⟩ => 3042  | ⟨0, _⟩, ⟨1, _⟩ => 3738  | ⟨0, _⟩, ⟨2, _⟩ => 3427
  | ⟨1, _⟩, ⟨0, _⟩ => 3431  | ⟨1, _⟩, ⟨1, _⟩ => 3072  | ⟨1, _⟩, ⟨2, _⟩ => 3787
  | ⟨2, _⟩, ⟨0, _⟩ => 3733  | ⟨2, _⟩, ⟨1, _⟩ => 3481  | ⟨2, _⟩, ⟨2, _⟩ => 2942

-- Vérification stochastique
#eval M3_counts ⟨0, by omega⟩ ⟨0, by omega⟩ +
      M3_counts ⟨0, by omega⟩ ⟨1, by omega⟩ +
      M3_counts ⟨0, by omega⟩ ⟨2, by omega⟩  -- 10207

-- Biais diagonal : M₃[i,i] × 3 < total
#eval M3_counts ⟨0, by omega⟩ ⟨0, by omega⟩ * 3 < 10207  -- true
#eval M3_counts ⟨1, by omega⟩ ⟨1, by omega⟩ * 3 < 10290  -- true
#eval M3_counts ⟨2, by omega⟩ ⟨2, by omega⟩ * 3 < 10156  -- true

end CouretUnification.ToyModelFloat
