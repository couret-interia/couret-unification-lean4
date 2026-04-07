import Mathlib.Data.Rat.Defs

namespace CouretUnification.Meta

def delta3SlopeEmpirical : ℚ :=
  (1889 : ℚ) / 5000

lemma delta3SlopeEmpirical_def :
    delta3SlopeEmpirical = (1889 : ℚ) / 5000 := by
  rfl

def sampleRatio : ℚ :=
  (3 : ℚ)

end CouretUnification.Meta