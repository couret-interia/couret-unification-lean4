/-
# CouretUnification/Logic/C3Weak_Gram.lean

Façade de compatibilité vers
`CouretUnification.Logic.H3.C3Weak_Gram`.

Ce fichier n'est plus canonique. La source de vérité est désormais :
`CouretUnification.Logic.H3.C3Weak_Gram`.
-/

import CouretUnification.Logic.H3.C3Weak_Gram

namespace CouretUnification.Logic.C3Weak_Gram

export CouretUnification.Logic.H3.C3Weak_Gram
  ( HasGramFactorization
    IsRigid
    IsRigid.toHasGramFactorization
    HasGramFactorization.toIsRigid
    gram_entry_eq_inner_Av
    semidef_of_gram_factor
    gram_quadratic_eq_inner_sum
    gram_quadratic_re_eq_norm_sq
    gram_semidef_of_rigid
    gram_semidef_of_rigid_real_part
    gram_semidef_of_isRigid
    HasGramFactorization.ofProjector
    fileIdentity )

end CouretUnification.Logic.C3Weak_Gram
