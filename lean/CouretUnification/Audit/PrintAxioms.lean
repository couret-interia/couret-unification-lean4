/-
CouretUnification.Audit.PrintAxioms
========================================================================

Copyright (c) 2026 Alexandre Couret. Tous droits réservés.

Audit/PrintAxioms.lean (v38x).

-/

import CouretUnification.Core.CenteredCoordinates
import CouretUnification.Logic.H3.SpectralBridge
import CouretUnification.ResGold.Status

namespace CouretUnification.Audit

-- PrintAxioms de SpectralBridge.lean
#print axioms CouretUnification.Logic.H3.conditional_bridge_closure
#print axioms CouretUnification.Logic.H3.conditional_bridge_closure_nondeg
#print axioms CouretUnification.Logic.H3.trivial_bridge_is_not_nondegenerate

-- PrintAxioms de CenteredCoordinates.lean (since v38.4.7)
#print axioms CouretUnification.Core.centered_29_eq_neg_sevenSum
#print axioms CouretUnification.Core.centered_ext_from_first_seven

-- PrintAxioms de ResGold.lean (since v38.5)
#print axioms CouretUnification.ResGold.rh_not_claimed

end CouretUnification.Audit
