# Registre Sophie Germain — Couret-Unification

## Sophie Germain / SG-shift — état v38x

- `Residue/SGShiftSqrt2.lean` : `[D]`
  - identité cubique rationnelle `M³ = (1/2)M`
  - forme entière `2M³ = M`
  - forme factorisée `M(2M² − I) = 0`
  - aucun `sorry`, aucun `Real.sqrt`

- `Residue/SGShiftSpectrum.lean` : `[O]`
  - frontière spectrale présente
  - aucun claim complet sur les valeurs propres
  - futur lieu de formalisation de `λ ∈ {0, ±1/√2}`

- `SophieGermainUmbrella.lean` :
  - regroupe le noyau SG stable
  - distingue `[D]`, `[M]`, `[O]`
  - préserve `RHClaimed = false`

## Fichiers

### Modules démontrés `[D]`

- `Core/SophieGermain.lean`
- `Core/SophieGermainHecke.lean`
- `Core/SophieGermainTowerLift.lean`
- `Residue/SGShiftSqrt2.lean`

### Modules empiriques `[M]`

- `Empirical/SophieGermainExpected.lean`
- `Empirical/SophieGermainTransitions.lean`
- `Numerics/ScanSummary.lean`
- `Numerics/UseScanSummary.lean`
  - façade de verdict numérique

### Frontières ouvertes `[O]`

- `Residue/SGShiftSpectrum.lean`
  - frontière spectrale
  - pas encore de preuve complète de `λ ∈ {0, ±1/√2}`
  - aucun `sorry`, aucun axiome

### Experimentaux `[D-toy] + [M]`

`Experimental/TowerLift/ToyModelSpec.lean` [D-toy] spécification formelle interne du modèle jouet
`Experimental/TowerLift/ToyModel.lean`     [D-toy] théorèmes du modèle jouet, si build sans axiome
`Experimental/TowerLift/ToyModelFloat.lean`    [M] numérique / flottant / expérimental

## Invariants doctrinaux

- `RHClaimed = false`
- `HilbertPolyaClaimed = false`
- `Det2IdentityClaimed = false`
- `L7Established = false`
