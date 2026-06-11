
# Résultats formels `[D]` — registre de synthèse

> Inventaire humain des résultats formels démontrés dans le périmètre `Frozen`.
>
> Ce registre n’est pas un compteur automatique de théorèmes Lean.
> Il agrège des familles de théorèmes en résultats mathématiques lisibles.

## Doctrine

Invariant constitutionnel :

```text
RHClaimed = false
```

Un résultat inscrit ici est `[D]` uniquement dans le périmètre indiqué :

* preuve Lean compilée ;
* zéro `sorry` dans le module gelé concerné ;
* pas de promotion vers RH, Hilbert–Pólya, `det₂ ↔ ξ`, ni appariement global des zéros ;
* statut relu humainement à partir de `build_reports/proved_theorems_frozen.txt`.

Les fichiers d’audit donnent des candidats. Ce registre donne les résultats retenus.

```text
inventaire brut ≠ registre scientifique
theorem Lean technique ≠ claim [D] autonome
```

---

## 1. Noyau fini `G₃₀`

### D-FIN-01 — Sommes de caractères sur sous-groupe quadratique

**Fichier porteur :**

```text
lean/CouretUnification/Core/CharacterSubgroupSums.lean
```

**Théorèmes porteurs :**

```text
quadraticProjectorC_eq_kerIndicatorC
trivial_on_ker_iff
sum_monoidHomChar_eq_zero
sum_over_ker_eq_zero
```

**Résultat :**

Formalisation de l’identité de projecteur quadratique et des sommes de caractères sur le noyau d’un caractère d’ordre 2.

**Statut :** `[D-formal, abstract]`.

**Portée :** groupe abélien fini abstrait, caractères vers `ℂˣ`.

---

### D-FIN-02 — Lemme du défaut ponctuel

**Fichier porteur :**

```text
lean/CouretUnification/Core/PointDefectLemma.lean
```

**Théorèmes porteurs :**

```text
energy_secondary_eq_one
energy_dominant
```

**Résultat :**

Dans un groupe abélien fini muni d’un caractère quadratique, retirer un point d’une fibre quadratique produit un spectre d’énergie à deux niveaux : dominante sur le caractère quadratique, secondaire uniforme sur les autres caractères non triviaux.

**Statut :** `[D-formal, abstract]`.

**Portée :** résultat fini général, indépendant de `G₃₀`.

---

### D-FIN-03 — Classification complète des 56 triplets de `G₃₀`

**Fichier porteur :**

```text
lean/CouretUnification/Core/G30Classification.lean
```

**Théorèmes porteurs :**

```text
dichotomy
count_Q
count_C
total_56
parseval_total_15
twoFixed_count
twoFixed_members
TC_is_typeQ
typeQ_iff_quadratic_fiber
```

**Résultat :**

Classification exhaustive des 56 triplets de `G₃₀` en deux familles :

```text
24 triplets de type Q
32 triplets de type C
```

avec conservation de l’énergie non triviale et identification du triplet Couret comme type Q.

**Statut :** `[D-computational, local]`.

**Portée :** calcul fini certifié par `native_decide`.

---

### D-FIN-04 — Pont formel entre type Q et fibre quadratique

**Fichier porteur :**

```text
lean/CouretUnification/Core/G30ClassificationFromPointDefect.lean
```

**Théorèmes porteurs :**

```text
typeQ_of_isTypeQTriplet
typeQ_implies_quadratic_fiber_of_mem
typeQTriplet_implies_quadratic_fiber
typeQ_implies_quadratic_fiber
```

**Résultat :**

Passage formel de la classification computationnelle des triplets de type Q vers leur interprétation comme fibres quadratiques privées d’un point.

**Statut :** `[D-formal, local bridge]`.

**Portée :** dépend du noyau computationnel `G30Classification`.

---

### D-FIN-05 — Résonance quadratique finie et dominance `3/5`

**Fichier porteur :**

```text
lean/CouretUnification/Core/QuadraticResonance.lean
```

**Théorèmes porteurs :**

```text
fourier_quadratic_dominant
fourier_other_nontrivial_eq_64
fourier_trivial_eq_zero
total_energy_eq_960
quadratic_resonance_three_fifths
chi_quadratic_eq_legendre_mod5
A4_pure_quadratic
kA4_eq_four_times_legendre
```

**Résultat :**

Formalisation finie d’une dominance quadratique : une part `3/5` de l’énergie non triviale est portée par le canal quadratique dans le modèle fini considéré.

**Statut :** `[D-formal / D-computational, finite]`.

**Portée :** résultat fini ; ne se transporte pas automatiquement aux premiers réels.

---

## 2. Chiralité finie modulo 30

### D-CHI-01 — Décomposition orbitale finie de `G₃₀`

**Fichier porteur :**

```text
lean/CouretUnification/Logic/ChiralityFinite.lean
```

**Théorèmes porteurs :**

```text
card_E
E_closed_under_mul
TC_subset_E
TC_auto_inverse
orbA_cycle
orbB_cycle
orbits_partition
orbits_disjoint
card_orbA
card_orbB
order_of_7
powers_of_7_eq_orbA
TC_splits
phantom_mul
phantom_19_not_in_TC
phantom_jumps_orbit
janus_involution_check
janus_pairs_cross_orbits
```

**Résultat :**

Décomposition finie des unités modulo 30 en deux orbites de taille 4, identification du rôle du générateur 7, du coset associé, du triplet Couret et du résidu fantôme 19.

**Statut :** `[D-formal, finite]`.

**Portée :** structure finie modulo 30.

---

### D-CHI-02 — Opérateur linéaire chiral `Ω₇`

**Fichier porteur :**

```text
lean/CouretUnification/Logic/ChiralityLinear.lean
```

**Théorèmes porteurs :**

```text
P7_order_four
Omega7_eq
Omega7_antisymmetric
trace_Omega7
Omega7_cubed_plus_four
Omega7_factored
trace_Omega7_squared
Omega7_kills_vA_plus
Omega7_kills_vA_minus
Omega7_kills_vB_plus
Omega7_kills_vB_minus
Omega7_e0
```

**Résultat :**

Construction et certification de l’opérateur chiral fini `Ω₇`, avec antisymétrie, trace nulle, identité polynomiale et action explicite sur les vecteurs orbitaux.

**Statut :** `[D-formal, finite linear algebra]`.

**Portée :** algèbre linéaire finie associée au modèle modulo 30.

---

## 3. Ponts eulériens et support squarefree

### D-EUL-01 — Facteur local squarefree et produit eulérien

**Fichier porteur :**

```text
lean/CouretUnification/Logic/EulerBridgeInfinite.lean
```

**Théorèmes porteurs :**

```text
e4_1_prime_pow_eq_zero
e4_2_prime_pow_tsum_eq_one_add
e3_1_summable_norm_of_domination
e3_2_summable_norm_of_nat_add_rpow_bound
e4_bridge_tprod
squarefree_limit_eq_euler_product
```

**Résultat :**

Fermeture du pont eulérien squarefree : facteur local, domination sommable, produit infini et identité de limite eulérienne dans le cadre formalisé.

**Statut :** `[D-formal, Euler bridge]`.

**Portée :** pont eulérien local/global contrôlé ; ne ferme pas `det₂ ↔ ξ`.

---

### D-EUL-02 — Compatibilité eulérienne

**Fichier porteur :**

```text
lean/CouretUnification/Logic/EulerBridgeInfiniteCompat.lean
```

**Théorèmes porteurs :**

```text
local_factor_squarefree_tsum
target_bound
target_bound_norm
target_bound_from_legacy_bound
```

**Résultat :**

Compatibilité technique entre les formulations du pont eulérien, avec normalisation des bornes et facteur local squarefree.

**Statut :** `[D-formal, compatibility]`.

**Portée :** résultat de support pour le pont eulérien.

---

### D-SQF-01 — Support squarefree multiplicatif

**Fichier porteur :**

```text
lean/CouretUnification/Logic/H3/SquarefreeSupport.lean
```

**Théorèmes porteurs :**

```text
coprime_prime_prod_subset
powerset_prod_disjoint
squarefree_mul_iff_of_coprime
squarefree_support_transfer
squarefree_support_transfer_real
isMultiplicative_norm_sq
sum_normSq_squarefree_eq_prod
```

**Résultat :**

Transfert du support squarefree dans un cadre multiplicatif fini et réel, avec produit sur support et factorisation de normes.

**Statut :** `[D-formal, squarefree support]`.

**Portée :** support arithmétique ; ne constitue pas une fermeture RH.

---

### D-SQF-02 — C-04a : minoration effective des squarefree

**Fichiers porteurs :**

```text
lean/CouretUnification/Logic/H3/SquarefreeDensityHalf.lean
lean/CouretUnification/Logic/H3/SquarefreeDensityC04aClosed.lean
```

**Théorèmes porteurs :**

```text
squarefreeCountGeHalfBridge_proved
squarefreeCount_ge_half_final
squarefreeCountGeHalfBridge_promoted
squarefreeCount_ge_half_unconditional
C04a_squarefree_half_promoted
squarefreeDensityC04aClosure_proved
```

**Résultat :**

Minoration effective :

```lean
∀ {N : ℕ}, 176 ≤ N → (N : ℚ) / 2 ≤ squarefreeCount N
```

**Statut :** `[D-formal, arithmético-effectif]`.

**Portée :** résultat effectif local sur les entiers squarefree.

---

### D-SQF-03 — C-04b : densité asymptotique `6 / π²`

**Fichiers porteurs :**

```text
lean/CouretUnification/Logic/H3/SquarefreeDensityAsymptotic.lean
lean/CouretUnification/Logic/H3/SquarefreeDensityC04bClosed.lean
```

**Théorèmes porteurs :**

```text
squarefree_asymptotic_density_final_proved
squarefreeAsymptoticDensitySixOverPiSquaredBridge_proved
squarefree_asymptotic_density_six_over_pi_squared
C04b_squarefree_density_closed
squarefreeAsymptoticDensityBridge_proved
squarefree_asymptotic_density_unconditional
C04b_squarefree_density_promoted
squarefreeDensityC04bClosure_proved
```

**Résultat :**

Densité asymptotique des entiers squarefree :

```text
squarefree density = 6 / π²
```

dans le cadre formalisé du dossier `SquarefreeDensity`.

**Statut :** `[D-formal, arithmético-analytique local]`.

**Portée :** densité squarefree ; ne ferme aucun pont global `ξ`.

---

## 4. Gram, facteurs locaux et ponts analytiques conditionnels

### D-GRAM-01 — Semi-définie positivité de Gram sous factorisation

**Fichier porteur :**

```text
lean/CouretUnification/Logic/H3/C3Weak_Gram.lean
```

**Théorèmes porteurs :**

```text
HasGramFactorization.toIsRigid
semidef_of_gram_factor
gram_quadratic_eq_inner_sum
gram_quadratic_re_eq_norm_sq
gram_semidef_of_rigid
gram_semidef_of_rigid_real_part
gram_semidef_of_isRigid
```

**Résultat :**

Formalisation du passage d’une factorisation de Gram à une forme semi-définie positive.

**Statut :** `[D-formal, conditional interface]`.

**Portée :** résultat conditionnel typé ; ne prouve pas RH.

---

### D-LOC-01 — Facteur local H3

**Fichier porteur :**

```text
lean/CouretUnification/Logic/H3/LocalFactor.lean
```

**Théorèmes porteurs :**

```text
local_factor_normSq
local_factor_normSq_bounds
local_factor_prime_half
local_factor_prime_sigma
```

**Résultat :**

Contrôle élémentaire du facteur local associé au front H3, avec bornes de norme et spécialisations en `σ = 1/2` ou `σ ≥ 0`.

**Statut :** `[D-formal, local factor]`.

**Portée :** brique locale ; ne ferme pas le pont analytique global.

---

### D-MOB-01 — Pont de Möbius local

**Fichier porteur :**

```text
lean/CouretUnification/Logic/H3/MoebiusBridge.lean
```

**Théorèmes porteurs :**

```text
moebius_LSeriesSummable_two
arithmetic_convolution_bridge
```

**Résultat :**

Pont local autour de la sommabilité de la série de Möbius en 2 et de la convolution arithmétique.

**Statut :** `[D-formal, local bridge]`.

**Note :**

Le théorème :

```text
LSeries_mu_at_two_project_target : True
```

est un témoin d’ancrage / placeholder trivial ; il n’est pas compté comme résultat scientifique autonome.

---

## 5. Ponts L6 et calibration temporelle

### D-L6-01 — Ponts `Aarch` et `Ztot`

**Fichier porteur :**

```text
lean/CouretUnification/Logic/L6Bridge.lean
```

**Théorèmes porteurs :**

```text
Aarch_bridge
Ztot_bridge
```

**Résultat :**

Ponts formels entre les interfaces `Aarch` et `Ztot` dans le cadre L6.

**Statut :** `[D-formal, bridge]`.

**Portée :** interface formalisée ; ne ferme pas les estimées analytiques globales.

---

### D-TIME-01 — Calibration canonique `B2`

**Fichier porteur :**

```text
lean/CouretUnification/Logic/TimeBridge/B2Calibration.lean
```

**Théorèmes porteurs :**

```text
exp_neg_two_t_canonical
B2_calibration_identity
t_canonical_characterization
```

**Résultat :**

Calibration exacte du paramètre canonique `t_canonical`, avec identité exponentielle et caractérisation associée.

**Statut :** `[D-formal, calibration]`.

**Portée :** brique de calibration ; aucun contenu RH.

---

## 6. Garde-fous doctrinaux formalisés

### D-GUARD-01 — Verrous ouverts et non-promotion RH

**Fichier porteur :**

```text
lean/CouretUnification/Logic/OpenLocks.lean
```

**Théorèmes porteurs :**

```text
no_rh_wall_lock_proved
L12_H3_no_strategy
```

**Résultat :**

Formalisation de garde-fous : le fait qu’un mur RH ne soit pas fermé et que certains verrous restent ouverts est inscrit dans le système.

**Statut :** `[D-doctrinal, guard]`.

**Portée :** invariant de discipline ; ce n’est pas une preuve mathématique de RH ni de son contraire.

---

## 7. Éléments explicitement non comptés comme résultats autonomes

Les éléments suivants apparaissent dans l’audit, mais ne doivent pas être comptés comme résultats `[D]` autonomes :

* lemmes privés purement techniques ;
* lignes `True := trivial` servant d’ancrage ;
* théorèmes de type `*_machine_anchor`;
* théorèmes de statut ou de façade sans contenu mathématique propre ;
* lemmes auxiliaires de réécriture, coercion, normalisation ou compatibilité ;
* compteurs `native_decide` très locaux lorsqu’ils ne portent pas un énoncé agrégé ;
* déclarations documentaires présentes dans les commentaires.

Exemples typiques :

```text
G30Classification_machine_anchor : True
AFourStatus_machine_verified : True
mellin_inversion_public_anchor : True
LSeries_mu_at_two_project_target : True
```

Ces lignes sont utiles architecturalement, mais ne sont pas des claims scientifiques autonomes.

---

## 8. Synthèse actuelle

À partir du périmètre `Frozen`, le registre retient actuellement :

```text
D-FIN    : 5 résultats
D-CHI    : 2 résultats
D-EUL    : 2 résultats
D-SQF    : 3 résultats
D-GRAM   : 1 résultat
D-LOC    : 1 résultat
D-MOB    : 1 résultat
D-L6     : 1 résultat
D-TIME   : 1 résultat
D-GUARD  : 1 résultat
```

Soit :

```text
18 résultats formels agrégés [D]
```

Ce nombre remplace avantageusement l’ancien seuil prudent :

```text
au moins 14 résultats [D]
```

mais il ne doit jamais être confondu avec :

```text
126 theorem/lemma dans Frozen
1784 theorem/lemma globaux
```

La formule recommandée pour les documents publics est donc :

```text
un socle formel d’au moins 18 résultats agrégés [D],
issus de 126 théorèmes/lemmes Lean dans le périmètre Frozen.
```

---

## 9. Formule canonique

```text
Le relief donne la forme.
Lean donne l’attestation locale.
Le registre donne le droit de dire [D].
RHClaimed reste false.
```
