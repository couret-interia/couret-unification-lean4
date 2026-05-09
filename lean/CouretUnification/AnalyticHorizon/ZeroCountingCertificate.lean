import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# ZeroCountingCertificate.lean

Active layer. Conditional certificate for the Riemann-von Mangoldt
style shell-counting obligation on the zero side.

This file does not prove Riemann-von Mangoldt. It does not identify
the abstract `Zero` type with the zeros of zeta. It records the
typed shape of the counting obligation.

It also exposes the canonical wrapper `ZeroSideSummabilityCertificate`
under which the audit and the torsion-zero interface refer to the
classical zero-counting obligation.

Doctrine:
- no RH claim;
- no Hilbert-Polya claim;
- no proof of Riemann-von Mangoldt;
- no closed explicit formula claim;
- the obligation is localized and conditional; it is not paid.

This file is a contract, not a theorem.
-/

namespace CouretUnification.AnalyticHorizon

/-- Abstract spectral data.

`Zero` is an abstract type. `gamma` is the ordinate function.
`zerosInShell k` is the set of zeros whose ordinate falls in some
implicit shell of level `k`.

No assertion is made that `Zero` is the type of zeros of the
Riemann zeta function; this is ONLY a typed receptacle. -/
structure ZeroShellData where
  Zero : Type
  gamma : Zero → ℝ
  zerosInShell : ℕ → Finset Zero

/-- Conditional certificate for shell-counting.

The obligation is that the number of zeros in shell `k` grows at
most logarithmically in `k`. This is the typed shape of
Riemann-von Mangoldt. It is not proved here. -/
structure ZeroCountingCertificate where
  data : ZeroShellData
  zeroSideSummable :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ,
      ((data.zerosInShell k).card : ℝ) ≤ C * Real.log ((k : ℝ) + 3)

/-- Canonical wrapper exposed as the Active "ZeroSide summability"
interface.

This is the type referenced by `ActiveLayerFullAudit` and by
`TorsionZeroInterfaceCertificate.zeroSide`. The wrapper holds the
underlying classical certificate without altering it. -/
structure ZeroSideSummabilityCertificate where
  zeroCounting : ZeroCountingCertificate

namespace ZeroSideSummabilityCertificate

/-- Forwarding accessor: the summability obligation lives in the
inner classical certificate. -/
def zeroSideSummable (cert : ZeroSideSummabilityCertificate) :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ,
      ((cert.zeroCounting.data.zerosInShell k).card : ℝ)
        ≤ C * Real.log ((k : ℝ) + 3) :=
  cert.zeroCounting.zeroSideSummable

end ZeroSideSummabilityCertificate

/- ══════════════════════════════════════════════════════════════
   Doctrinal flags.
   ══════════════════════════════════════════════════════════════ -/

/-- The zero side is NOT declared closed by this certificate. -/
def ZeroSideClosedFromZeroCountingCertificate : Bool := false

/-- Riemann-von Mangoldt is NOT claimed proved by this certificate. -/
def RiemannVonMangoldtClaimedFromCertificate : Bool := false

/-- No RH consequence is exported. -/
def RHFromZeroCountingCertificate : Bool := false

/-- No Hilbert-Polya consequence is exported. -/
def HilbertPolyaFromZeroCountingCertificate : Bool := false

/-- No explicit formula closure is exported. -/
def ExplicitFormulaClosedFromZeroCountingCertificate : Bool := false

/- ══════════════════════════════════════════════════════════════
   Tautological accessors.
   ══════════════════════════════════════════════════════════════ -/

/-- Tautological access to the classical shell-counting obligation. -/
theorem zeroCounting_has_log_shell_bound
    (cert : ZeroCountingCertificate) :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ,
      ((cert.data.zerosInShell k).card : ℝ) ≤ C * Real.log ((k : ℝ) + 3) :=
  cert.zeroSideSummable

/-- Tautological access to the wrapped summability certificate. -/
theorem zeroSideSummability_has_log_shell_bound
    (cert : ZeroSideSummabilityCertificate) :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ,
      ((cert.zeroCounting.data.zerosInShell k).card : ℝ)
        ≤ C * Real.log ((k : ℝ) + 3) :=
  cert.zeroSideSummable

end CouretUnification.AnalyticHorizon
