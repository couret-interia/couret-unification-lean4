import CouretUnification.Core.SpectralProfile

namespace CouretUnification.Core

/-- Dominant and non-dominant finite spectral values in the toy profile. -/
def dominantValue : Int := 9
def secondaryValue : Int := 1

lemma dominant_gt_secondary : dominantValue > secondaryValue := by
decide

end CouretUnification.Core
