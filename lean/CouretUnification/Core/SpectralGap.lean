import CouretUnification.Core.SpectralProfile

namespace CouretUnification.Core

/-- Valeurs spectrales finies dominante et non dominante dans le profil jouet. -/
def dominantValue : Int := 9
def secondaryValue : Int := 1

lemma dominant_gt_secondary : dominantValue > secondaryValue := by decide

end CouretUnification.Core
