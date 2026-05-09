import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# SoinInterface.lean

Active layer. Structural / categorical interface.

This file does not prove the "mother theorem" and does not claim
that any of the seven axes of the synthesis is an instance of a
faithful functor.  It packages the interface that such a statement
would require, as a typed obligation.

Doctrine:
- no RH claim;
- no Hilbert-Polya claim;
- no spectral coincidence claim;
- no closed explicit formula claim;
- no determinant identity claim;
- no mother theorem claim;
- the negative empirical result nu_eff ≈ 0.27 ≠ 1/sqrt 7 is
  preserved as an open obligation and is not reinterpreted here
  as a fidelity signature of the functor;
- no axis is declared a proved instance of the functor.

This file is a contract, not a theorem.
-/

namespace CouretUnification.AnalyticHorizon.Soin

open CategoryTheory

/-- An `AsymCategory` is a category in which morphisms encode
irreversibility: if both `X ⟶ Y` and `Y ⟶ X` exist, then `X = Y`.

This is a minimal, non-committal modelling of the "arrow of time"
category used by axis VI.  It does not assert that this category
corresponds to any specific physical or arithmetic structure. -/
class AsymCategory (C : Type*) extends Category C where
  irreversible :
    ∀ {X Y : C}, (X ⟶ Y) → (Y ⟶ X) → X = Y

/-- An `InvCategory` is a category that behaves as a groupoid:
every morphism is an isomorphism.

This is a minimal modelling of the "invariant layer" used as the
target of the Soin functor.  It does not commit to the specific
identity of the invariants (spectral ordinates, λ, topological
invariants, etc.). -/
class InvCategory (D : Type*) extends Category D where
  is_groupoid : ∀ {X Y : D} (f : X ⟶ Y), IsIso f

/-- Conditional certificate for a `Soin` functor.

This structure records the obligation that a faithful functor
`F : C ⥤ D` exists between an `AsymCategory` and an `InvCategory`.
It does not prove the existence of such a functor for any
particular instantiation.

Supplying a `SoinFunctorCertificate` is the prerequisite, not the
conclusion, of the mother-theorem obligation. -/
structure SoinFunctorCertificate
    (C D : Type*) [AsymCategory C] [InvCategory D] where
  F           : C ⥤ D
  is_faithful : Functor.Faithful F

/-- Open obligation corresponding to the negative empirical result
ν_eff ≈ 0.27 ≠ 1/√7 (metamaterial Poisson track).

Held as `Prop` fields to record that this discrepancy is NOT yet
reconciled.  It is explicitly NOT a proof that the discrepancy is
the "fidelity signature" of a Soin functor. -/
structure NuEffObligation where
  discrepancy_observed        : Prop
  reconciliation_status_open  : Prop

/-- The seven axes of the synthesis, kept as independently typed
open obligations.  None of these fields asserts that the corresponding
axis IS an instance of a Soin functor; each field is a separately
typed, currently unpaid obligation. -/
structure SevenAxesObligations where
  axis_I_wear_obligation            : Prop
  axis_II_separation_obligation     : Prop
  axis_III_cicatrisation_obligation : Prop
  axis_IV_debt_obligation           : Prop
  axis_V_repair_obligation          : Prop
  axis_VI_time_reversal_obligation  : Prop  -- condition of possibility
  axis_VII_pharmakon_obligation     : Prop

/-- The mother-theorem certificate.

This is NOT a proof of a mother theorem.  It is the typed shape
that a future proof would have to supply: a Soin functor certificate,
the seven axis obligations, and an explicit open ν_eff obligation.

No axis is asserted to be a proved instance of `soin`. -/
structure MotherTheoremCertificate
    (C D : Type*) [AsymCategory C] [InvCategory D] where
  soin   : SoinFunctorCertificate C D
  axes   : SevenAxesObligations
  nu_eff : NuEffObligation

/- ══════════════════════════════════════════════════════════════
   Doctrinal flags.  All claim-flags are `false` by construction.
   `NuEffNegativeResultPreserved` is `true` on purpose: it is the
   epistemic interdiction materialised in code.
   ══════════════════════════════════════════════════════════════ -/

/-- The mother theorem is not claimed to be proved. -/
def MotherTheoremClaimed : Bool := false

/-- No axis is declared a proved instance of a Soin functor. -/
def SevenAxesInstancesProved : Bool := false

/-- The empirical discrepancy ν_eff ≈ 0.27 ≠ 1/√7 is preserved as
a negative result.  This flag is deliberately `true`. -/
def NuEffNegativeResultPreserved : Bool := true

/-- The discrepancy has NOT been resolved as a "fidelity signature"
of the Soin functor.  This flag is `false` on purpose. -/
def NuEffResolvedAsFunctorSignature : Bool := false

/-- No RH consequence is exported from this interface. -/
def RHFromSoinInterface : Bool := false

/-- No Hilbert-Polya consequence is exported from this interface. -/
def HilbertPolyaFromSoinInterface : Bool := false

/-- No spectral coincidence is claimed by this interface. -/
def SpectralCoincidenceFromSoinInterface : Bool := false

/-- No closed explicit formula consequence is exported. -/
def ExplicitFormulaClosedFromSoinInterface : Bool := false

/-- No determinant identity is claimed by this interface. -/
def Det2IdentityFromSoinInterface : Bool := false

/- ══════════════════════════════════════════════════════════════
   Tautological accessors.  All structural and analytic work is
   carried by the certificate fields themselves.
   ══════════════════════════════════════════════════════════════ -/

/-- Tautological access to the Soin functor certificate.
Returns the certificate, not a proof that it is instantiated by
any concrete categories. -/
def mother_has_soin
    {C D : Type*} [AsymCategory C] [InvCategory D]
    (cert : MotherTheoremCertificate C D) :
    SoinFunctorCertificate C D :=
  cert.soin

/-- Tautological access to the faithfulness witness. -/
theorem soin_is_faithful
    {C D : Type*} [AsymCategory C] [InvCategory D]
    (cert : MotherTheoremCertificate C D) :
    Functor.Faithful cert.soin.F :=
  cert.soin.is_faithful

/-- Tautological access to the ν_eff obligation.  This is NOT a
proof that ν_eff is the fidelity signature of the functor. -/
def mother_has_nuEff_obligation
    {C D : Type*} [AsymCategory C] [InvCategory D]
    (cert : MotherTheoremCertificate C D) :
    NuEffObligation :=
  cert.nu_eff

/-- Tautological access to the seven axis obligations.  This is
NOT a proof that the axes are instances of the Soin functor. -/
def mother_has_seven_axes_obligations
    {C D : Type*} [AsymCategory C] [InvCategory D]
    (cert : MotherTheoremCertificate C D) :
    SevenAxesObligations :=
  cert.axes

end CouretUnification.AnalyticHorizon.Soin
