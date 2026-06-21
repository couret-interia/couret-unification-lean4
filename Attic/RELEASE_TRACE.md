# RELEASE_TRACE — v36.0-proof-jurisdiction

This release is a **proof jurisdiction**, not a proof of the Riemann
Hypothesis. It freezes the architectural state of the
Couret–Unification programme into a Lean 4 sanctuary that future
contributors must respect.

---

## Canonical invariants

- Frozen core: no `sorry`, no `axiom`, no `admit`.
- PrimeSide has the first Frozen compact-support closure.
- Archimedean, ZeroSide, Det2, torsion, and torsion-zero transfer remain Active obligations.
- Torsion is structural, not measurement noise.
- Torsion changes the clock, not the zeros.
- ZeroCounting remains neutral and classical.
- Pullback counting remains an unpaid obligation.

---

## Forbidden reinterpretations

Any future contributor must **never**:

1. Classify `nu_eff ≈ 0.27` as measurement noise.
2. Collapse `nu_eff` into `1/√7` to "fix" the gap.
3. Move the torsion certificate from Active to Frozen.
4. Redefine `ZeroCountingCertificate` through the torsion map.
5. Import an Active module from a Frozen file.
6. Set any `*Claimed*` flag to `true` without a complete formal
   proof replacing the corresponding Active obligation.
7. Infer RH, Hilbert–Polya, spectral coincidence, an explicit-formula
   closure, a determinant identity, or Riemann–von Mangoldt from this
   release alone.

---

## Required reopening protocol

1. Verify tag signature.
2. Record Lean, Lake, Mathlib, and repository commits in `RELEASE_ENV.txt`.
3. Run all audit scripts:
   ```bash
   bash scripts/audit_v36.0.sh
   bash scripts/audit_v36_torsion.sh
   bash scripts/audit_v36.9.sh
   ```
   All must exit 0.
4. Preserve all `false` doctrinal flags unless a complete formal
   Lean proof replaces the corresponding Active obligation in the
   same commit.

---

## Architectural map (v36.0 Frozen + v36.1–v36.10 Active+Manifest)

    Frozen core   Logic/ExplicitFormula/   (v36.0)
                  AnalyticHorizon/A8       (Frozen annex)

    Active        AnalyticHorizon/
                    ArchimedeanDigammaCertificate     v36.1
                    ZeroCountingCertificate           v36.2
                                                      (+ ZeroSideSummabilityCertificate wrapper)
                    ExplicitFormulaBridgeAudit        v36.3
                    Det2TransportCertificate          v36.4
                    SoinInterface                     v36.6
                    ArchimedeanTorsionCertificate     v36.7
                    TorsionZeroTransferCertificate    v36.8
                                                      (+ TorsionAnalyticObligation)
                    ActiveLayerFullAudit              v36.9

    Manifest      Release/ReleaseManifest             v36.10

    Audit         scripts/audit_v36.0.sh
                  scripts/audit_v36_torsion.sh
                  scripts/audit_v36.9.sh

The Frozen core is structurally separated from every Active module
by the import doctrine: Frozen never imports Active. The audit
scripts enforce this mechanically.

---

## Torsion analytic obligation (v36.8)

The pullback interface is gated by a dedicated structure
`TorsionAnalyticObligation` carrying four `Prop`-typed obligations:

- (T.1) `monotone : StrictMono φ_τ`
- (T.2) `bi_lipschitz_lower` — lower bi-Lipschitz with constant `c > 0`
- (T.3) `bi_lipschitz_upper` — controlled distortion (polynomial Lipschitz constant)
- (T.4) `polynomial_growth` — envelope `|φ_τ(t)| ≤ A·(1+|t|)^q`

None of these is proved here. They constitute the analytic debt of
the pullback and are auditable textually by `audit_v36_torsion.sh`.

---

## Canonical phrase

> v36 ne prouve pas l'Hypothèse de Riemann ; il construit la
> juridiction dans laquelle une future preuve devra déposer ses
> certificats. Le PrimeSide possède une première fermeture Frozen,
> tandis que les dettes archimédienne, spectrale, déterminantielle,
> torsionnelle et de transfert zéro sont localisées, typées et
> auditables, sans être déclarées payées.

> v36 does not prove the Riemann Hypothesis. It builds the
> jurisdiction in which a future proof must deposit its certificates.
> The PrimeSide has a first Frozen closure, while the Archimedean,
> spectral, determinantal, torsion, and zero-transfer debts are
> localized, typed, and auditable, without being declared paid.

---

*Pour Bernard Couret (1928–1999, Istres).*
