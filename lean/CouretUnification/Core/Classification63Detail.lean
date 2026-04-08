import CouretUnification.Core.Classification63
import Mathlib.Tactic

namespace CouretUnification.Core
namespace Classification63Detail

/-!
# Ventilation des 63 sous-ensembles à spectre entier par cardinalité
-/

open Classification63

def popcount (mask : Nat) : Nat :=
  (List.finRange 8).countP fun i => bitSet mask i

def intSpecByCard (k : Nat) : Nat :=
  (List.range 255).countP fun m => hasIntSpec (m + 1) && (popcount (m + 1) == k)

def totalByCard (k : Nat) : Nat :=
  (List.range 255).countP fun m => popcount (m + 1) == k

-- Discover actual values
#eval intSpecByCard 1  -- ?
#eval intSpecByCard 2  -- ?
#eval intSpecByCard 3  -- ?
#eval intSpecByCard 4  -- ?
#eval intSpecByCard 5  -- ?
#eval intSpecByCard 6  -- ?
#eval intSpecByCard 7  -- ?
#eval intSpecByCard 8  -- ?

-- Verify sum = 63
theorem ventilation_sum :
    intSpecByCard 1 + intSpecByCard 2 + intSpecByCard 3 + intSpecByCard 4 +
    intSpecByCard 5 + intSpecByCard 6 + intSpecByCard 7 + intSpecByCard 8 = 63 := by
  native_decide

-- TC verification
theorem TC_card : popcount couretMask = 3 := by native_decide
theorem TC_int_spec : hasIntSpec couretMask = true := by native_decide

end Classification63Detail
end CouretUnification.Core