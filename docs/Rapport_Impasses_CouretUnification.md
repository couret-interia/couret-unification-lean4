# Rapport des impasses — programme Couret-Unification

**Version** : ébauche 2026-04-24
**Invariant doctrinal** : `RHClaimed = false` · `HilbertPolyaClaimed = false` · `PhysicalLawClaimed = false`
**Objet** : inventaire typé des impasses, corrections et réfutations identifiées au fil du programme, pour servir de registre d'auto-falsification.
**Usage** : Partie A rédigée à partir de `conversation_search` + userMemories + fichiers en main. Partie B en grille à compléter par A. Couret avec les références externes (manuscrits, notes Thomas, logs PARI/GP, archives JR Consulting).

---

## Préambule méthodologique

### Périmètre de la Partie A

Les entrées de la Partie A satisfont toutes trois critères :

1. **Trace conversationnelle retrouvée** — je fournis l'URI du chat source (au format `claude.ai/chat/<uuid>`) pour chaque impasse.
2. **Contenu technique reproductible** — énoncé avant/après, mécanisme de détection, correction appliquée.
3. **Leçon méthodologique extraite** — ce que l'erreur a appris au programme au-delà de sa correction locale.

### Limites explicites

- Je n'ai pas accès aux manuscrits Bernard Couret, aux notes de laboratoire papier, aux échanges Slack/mail avec Thomas, ni aux archives JR Consulting. Les impasses référencées dans ces canaux figurent dans la Partie B.
- Les conversations parallèles menées via Gemini, GPT ou Claude Code ne sont pas recherchables depuis cette session. Certaines dates peuvent donc être antérieures à la date affichée (première fois qu'une erreur apparaît dans mes transcripts, pas forcément première détection).
- Je ne certifie pas l'exhaustivité. Je certifie que chaque item de la Partie A est sourcé.

### Typologie des impasses

| Type | Description | Exemples |
|---|---|---|
| **R — Retractation** | Un résultat annoncé est faussement affirmé | Lock 2 résolu → encodé |
| **C — Correction** | Une chaîne argumentative utilise un mauvais outil | Schur(V) → ‖M‖_HS |
| **N — No-go** | Une route d'attaque est éliminée quantitativement | 5 routes Lock 3 |
| **B — Bug** | Une erreur d'implémentation masquait un problème réel | channel_balance v7 |
| **A — Artefact** | Un résultat numérique est un sous-produit du modèle, pas une mesure | B2 t_equil |
| **T — Terminologie** | Confusion d'objets distincts sous une même étiquette | M₄ 15 vs 21 |

---

## Partie A — Impasses documentées (13 entrées)

### A1 — Spectre de Fourier de TC (type R) — mars 2026

**Source** : `claude.ai/chat/5632ef63-654f-4856-aeff-2daadcab5140` (30 mars 2026).

**Énoncé erroné (avant)** : Spec(A_TC) = {3, 3, 1, 1, 1, 1, 1, 1}, toutes valeurs propres positives.

**Énoncé correct (après)** : Spec(A_TC) = {3, 3, 1, 1, 1, 1, **−1, −1**}. Deux valeurs propres négatives. L'opérateur **n'est pas** positif-défini.

**Invariants préservés** : Parseval = Tr(A²) = 24 reste exact. Tr(A) = 8, Tr(A³) = 56, Tr(A⁴) = 168 également certifiés ensuite par `native_decide`.

**Conséquences doctrinales** : L'affirmation « TC est un système d'énergie positive » est invalidée. La décomposition spectrale correcte est {3² (dominant), 1⁴ (unité), (−1)² (anti-unité)}, avec classification en trois régimes chiralité/antichiralité dans les développements ultérieurs.

**Leçon** : une table de valeurs propres annoncée sans vérification `native_decide` n'est pas un fait Lean — c'est une espérance.

---

### A2 — Fausses extinctions spectrales (type R) — mars 2026

**Source** : `claude.ai/chat/5632ef63-654f-4856-aeff-2daadcab5140` (30 mars 2026) ; corroboré dans `claude.ai/chat/5b93b7e5-c0b4-42fd-9b09-17d53bd3a199`.

**Énoncé erroné (avant)** : Deux coefficients c_χ s'annulent dans la décomposition F(s) = Σ c_χ L(s,χ) — précisément les caractères quadratiques mod 3 et mod 5. Conséquence affichée : « TC est aveugle aux discriminants 3 et 5 ».

**Énoncé correct (après)** : **Aucun coefficient ne s'annule**. Les 8 valeurs sont exactement {3/8, 3/8, −1/8, −1/8, 1/8, 1/8, 1/8, 1/8}. Toutes contribuent à la décomposition.

**Conséquences doctrinales annulées** :

- L'explication du rang PCA ≈ 6.9 par « 6 caractères actifs » est invalidée.
- L'affirmation que TC est « aveugle aux discriminants 3 et 5 » est retirée.
- Toute la narration « extinction → signature arithmétique » est reclassée comme sur-interprétation.

**Leçon** : un coefficient proche de zéro numériquement ≠ un coefficient structurellement nul. La distinction est doctrinale, pas rhétorique.

---

### A3 — « Lock 2 résolu » requalifié « Lock 2 encodé » (type R) — mars 2026

**Source** : `claude.ai/chat/5b93b7e5-c0b4-42fd-9b09-17d53bd3a199` (ligne de synthèse des erreurs).

**Énoncé erroné (avant)** : « Lock 2 est résolu : la décomposition F(s) = Σ c_χ L(s,χ) donne la complétion eulérienne ».

**Énoncé correct (après)** : La décomposition F(s) = Σ c_χ L(s,χ) est un **fait standard d'algèbre linéaire finie** (projection sur la base de caractères de G₃₀). Ce n'est **pas** un théorème analytique nouveau. Le statut correct est « Lock 2 encodé » (formulé en termes de L-fonctions) et non « Lock 2 résolu ».

**Position dans l'architecture** : le Lock 2 lui-même sera ultérieurement **dissous** (mais par un tout autre mécanisme, cf. A6) comme tautologie de Hadamard, pas par cette décomposition.

**Leçon** : l'encodage d'un problème dans un formalisme (L-fonctions, caractères) ne constitue pas sa résolution ; la nomenclature doit refléter cette distinction sous peine de faux signal de progrès.

---

### A4 — Correction v17→v18 : Schur(V) → ‖M‖_HS (type C) — mars 2026

**Sources** :
- `claude.ai/chat/a2e18ff8-5228-4ced-8825-415808171e5d` (20 mars 2026) — calcul numérique
- `claude.ai/chat/b98f4249-1d5b-48f3-acb9-16ac98b46b33` — formalisation Lean H1
- `claude.ai/chat/e72a745d-87f7-4bca-99f7-2cee93e1a6db` — remarque Fermi/Latex

**Raisonnement erroné (v17)** : Appliquer directement le test de Schur à V, puis invoquer P(σ) = Σ p^(−σ) pour borner ‖V‖_HS.

**Erreur identifiée** : P(σ) converge pour σ > 1, **pas** pour σ > 1/2. À σ = 1/2, ‖V‖_HS diverge :

| σ | Scaling β de ‖V‖_HS | V ∈ S₂ ? |
|---|---|---|
| 0.50 | β = 0.416 | **NON** (diverge) |
| 0.75 | β = 0.143 | NON (diverge lentement) |
| 1.00 | β = 0.019 | OUI (converge) |

**Outil correct (v18)** : Utiliser l'opérateur conjugué

  M = (H₀ + I)^(−1/2) · V · (H₀ + I)^(−1/2)

et borner **‖M‖_HS**, pas ‖V‖_HS. Matrice d'entrées :

  M_{pq} = sinc(log(p/q)/w₀) / ((pq)^(σ/2) · √((p+1)(q+1)))

**Résultat préservé** : ‖M‖_HS ≤ P(σ+1) ≤ P(3/2) = **0.8495 < 1** pour σ ≥ 1/2. La chaîne KLMN est reconstruite intégralement avec cette borne. L'auto-adjonction de H = H₀ + V tient pour tout σ > 0.

**Point fin** : l'auto-adjonction ne requiert **pas** l'appartenance à S₂. Pour 1/2 ≤ σ ≤ 1, V ∉ S₂ mais M ∈ S₂ et det₂(I − zM) reste défini.

**Leçon** : un test spectral (Schur, KLMN, HS) s'applique à un opérateur précis. Changer l'opérateur de référence (V vs M = R^(1/2)VR^(1/2)) change la borne ; oublier cette distinction est l'erreur canonique dans les extensions d'opérateurs perturbés.

---

### A5 — Cinq routes éliminées vers Lock 3 (type N) — déc. 2025 à avril 2026

**Sources principales** :
- `claude.ai/chat/28aa502e-57b5-42c5-8a03-9b37f7760674` (10 avril 2026) — récap Lean
- `claude.ai/chat/ee889b05-da76-4d60-9776-d04478382cfb` (23 avril 2026) — théorème d'obstruction L10
- `claude.ai/chat/9326de57-6e08-4e97-a54e-276fc90cb89b` (23 avril 2026) — partie VII du dossier unifié

Cinq routes naïves vers l'opérateur de Hilbert-Pólya ont été testées puis éliminées avec **diagnostic chiffré** :

| # | Route | Tentative | Raison du rejet |
|---|---|---|---|
| N1 | Multiplicative | S_q = M_q ⊗ Id, Spec = {3²,1⁴,(−1)²} | Spectre entier, cible Spec_target = {±1/γ_n} ⊂ irrationnels transcendants (Hadamard) |
| N2 | sinc · χ₃₀ | S_q(s) = sinc(s)·χ₃₀(s) | Ratio A/B des coefficients de Hadamard diverge à **10¹¹** (k=2 : −1.73 ; k=12 : 1.85·10⁵) |
| N3 | Connes naïf | S_q = Σ log(p)/√p · T_p | Exposant spectral γ^(−0.33) observé, cible γ^(−1) (facteur 3 de décalage) |
| N4 | Berry-Keating | S_q = (xp + px)\|_{Λ_q} | Non-compact, spectre continu, incompatible avec det₂ |
| N5 | Kurtosis-collapse µ_k → δ₁ | Collapse vers Dirac | M₄ = 21 (pas M₂² = 9), kurtosis 7/3 ≠ 1, réfutation numérique exacte |

**Formalisation** : cristallisées dans le théorème d'obstruction **L10** (`Logic/H3/Lock3.lean` ou `L10NoGoTheorem.lean`), qui formalise qu'aucune limite faible d'une suite de spectres entiers ne peut capturer `Spec_target` sans enrichissement externe.

**Conséquence structurelle** : ces cinq routes ne sont pas des échecs honteux mais des **résultats négatifs publiables**. Elles réduisent l'espace de recherche et forcent les routes restantes (Connes adélique, Guinand-Weil top-down, tour Hecke enrichie) à porter une charge analytique externe explicite — ce qui revient à supposer une structure type Hilbert-Pólya déjà connue.

**Leçon** : un no-go formel chiffré vaut plus qu'un « peut-être ». Documenter pourquoi une route échoue avec des ordres de grandeur précis (A/B → 10¹¹, γ^(−0.33) vs γ^(−1)) protège le programme de revenir à ces routes par oubli.

---

### A6 — Lock 2 dissous comme tautologie Hadamard (type C, tardive) — avril 2026

**Sources** :
- `claude.ai/chat/c79a1154-60d1-4588-8647-9307cf8ac596`
- `claude.ai/chat/28aa502e-57b5-42c5-8a03-9b37f7760674` — preuve Lean structurée
- `claude.ai/chat/5cb19a95-7029-42a8-9af8-6a43a8f6a794` (5 avril 2026) — session clé

**Statut antérieur** : Lock 2 (complétion eulérienne globale) était traité comme un verrou **indépendant** à prouver, nécessitant une chaîne analytique propre.

**Statut corrigé** : Lock 2 est dissous comme **tautologie conditionnelle à Lock 3**. La chaîne (A)→(B)→(C) :

1. **(A) Hadamard 1893** : ξ(s) entière d'ordre 1, genre 1 → produit de Weierstrass.
2. **(B) B₁ = 0** : conséquence algébrique pure de ξ(s) = ξ(1−s). Preuve : B₁·s = B₁·(1−s) ∀s ⟹ B₁ = −B₁ ⟹ B₁ = 0.
3. **(C) Appariement ±γ** : pour un spectre symétrique {±1/γ_n}, les facteurs exp(z/γ_n)·exp(−z/γ_n) = 1 s'annulent, laissant ∏_n (1 − z²/γ_n²).

**Résultat** : si Lock 3 donne Spec(S) = {±1/γ_n}, alors det₂(I−zS) = (1/ξ(1/2)) · ξ(1/2 + iz) **automatiquement**. Normalisation C = 1/ξ(1/2) ≈ 2.01158 vérifiée numériquement à 50 chiffres.

**Vérification σ_k** (500 zéros) :

| k | Ratio σ_k^C / σ_k^B | Convergence |
|---|---|---|
| 2 | 0.9503 | queue lente ~ log²N/N |
| 4 | 0.99957 | 99.98% |
| 6 | 0.99999989 | 99.999+% |
| 8–12 | ≥ 0.9999999999 | machine precision |

**Leçon** : un verrou identifié par une narration n'est pas toujours un verrou logique. Le faire sauter revient parfois à reformuler, pas à prouver. Seul le Lock 3 (existence de l'opérateur Hilbert-Pólya) porte la charge analytique réelle ; le programme se réduit à **un seul sorry irréductible** (`lock3_operator_exists`, logiquement équivalent à RH).

---

### A7 — Bug E = 3 à L5 : safe tower skipping (type B + C) — avril 2026

**Sources** :
- `claude.ai/chat/3d1701ab-562a-41cf-a05b-33df0e074d21` (5 avril 2026) — découverte
- `claude.ai/chat/28721eca-8c86-4966-b78c-ccdb4fb05b9b` (6 avril 2026) — correction Lean v28

**Énoncé erroné** : « L'invariant E = Parseval/φ(q) = 3 tient sur toute la tour primoriale L3, L4, L5, L6, ... »

**Détection** : calcul direct à L5 (modulus q = 2310).

  | Niveau | q | φ(q) | Parseval | E = Parseval/φ |
  |---|---|---|---|---|
  | L3 | 30 | 8 | 24 | 3 ✓ |
  | L4 | 210 | 48 | 144 | 3 ✓ |
  | L5 | 2310 | 480 | **960** (pas 1440) | **2** (pas 3) |

**Cause racine** : TC = {1, 11, 29}, et **11 divise 2310**. Donc χ(11) = 0 pour tout caractère χ mod 2310 (imprimitivité forcée). La somme c_χ = χ(1) + χ(11) + χ(29) perd un terme.

**Correction doctrinale** : E = 3 est un invariant de la **tour sûre** qui saute les premiers p ∈ {11, 29} (les éléments non-triviaux de TC). La tour sûre commence à L3 = 30, passe à L4 = 210 (2·3·5·7), puis saute 11 et passe à 2310/11 = 210 × 13 = 2730 (ou similaire selon convention). Le pack Lean v28 intègre l'hypothèse `29 < p` déjà présente, rendant la correction cohérente.

**Collatéral** : la formule fermée `L_k = 2 + (4 + 2(−1)^k)/3^k` est établie pour L3 ; le transport CRT du **second moment** est prouvé (`M₂ = 3` invariant par multiplicativité commune de φ et Parseval) ; les moments supérieurs ne sont pas CRT-invariants.

**Leçon** : un invariant doit être vérifié numériquement au-delà du niveau où il est conjecturé. Les divisibilités d'éléments de TC par le modulus sont des obstructions structurelles qui apparaissent brutalement au niveau où le premier « p ∈ TC » est absorbé.

---

### A8 — Confusion M₄ : 15 vs 21 (type T) — avril 2026

**Source** : `claude.ai/chat/5b93b7e5-c0b4-42fd-9b09-17d53bd3a199` (session `Kurtosis.lean`, v32.7).

**Confusion** : le nombre 15 circulait dans la synthèse comme « M₄ » ou « 4ème moment ». Le nombre 21 apparaissait dans les preuves Lean. Les deux sont corrects, **mais désignent des objets différents**.

**Clarification** (certifié par `native_decide`) :

| Quantité | Valeur | Définition |
|---|---|---|
| Tr(A) | 8 | trace |
| Tr(A²) = Parseval | 24 | norme² Frobenius |
| Tr(A³) | 56 | — |
| Tr(A⁴) | 168 | — |
| M₂ = Tr(A²)/8 | **3** | 2ème moment spectral brut |
| **M₄ = Tr(A⁴)/8** | **21** | **4ème moment spectral brut** |
| κ_raw = M₄/M₂² | **7/3** | kurtosis brute |
| P − ρ² (masse non-triviale) | **15** | Parseval moins valeur propre dominante² = 24 − 9 |
| (P − ρ²)/M₂² | **5/3** | **ratio de masse non-triviale** (≠ kurtosis) |
| σ² centrale | 2 | variance autour de μ = 1 |
| μ₄/σ⁴ centrale | 2 | kurtosis centrée |
| Excess kurtosis | −1 | sous-gaussien |

**Résolution** : le « 15 » de la synthèse est la **masse de Parseval non triviale** (24 − 9), pas le 4ème moment. Le ratio « 5/3 » est (P − ρ²)/M₂² = 15/9, pas la kurtosis M₄/M₂² = 21/9 = 7/3. La réfutation de µ_k → δ₁ (entrée N5 dans A5) utilise la kurtosis **brute** = 7/3 ≠ 1, donc la réfutation reste valide, mais la mention « M₄ = 15 » dans les documents antérieurs est à corriger en « P − ρ² = 15 ».

**Leçon** : quand deux nombres (15 et 21) circulent sous la même étiquette (« M₄ »), il y a soit un bug, soit une terminologie floue. Ici c'est la terminologie. Un fichier `Kurtosis.lean` avec table explicite des définitions résout la confusion définitivement.

---

### A9 — Bug `channel_balance_v7_2d.gp` : chareval + imprimitivité (type B) — avril 2026

**Source** : `claude.ai/chat/fa7412ba-0083-485e-aa4d-7c0c0bcc224e` (8 avril 2026).

**Script PARI/GP** : `channel_balance_v7_2d.gp`. Calcule la balance canonique R_χ(σ) = −2 Re(L'/L(σ,χ)) − S_χ(σ) sur les 8 caractères primitifs du groupe (ℤ/30ℤ)×, devant converger vers 0 pour σ > 1.

**Évolution v7.1 → v7.2d** — deux bugs successifs :

1. **v7.1 → v7.2a-c** : `chi_1(n) = if(gcd(n,30)==1, 1, 0)` masquait le pôle archimédien du canal principal. Corrigé en `chi_1(n) = 1`.

2. **v7.2a-c → v7.2d** : **`chareval` dans PARI/GP retourne un rationnel r**, pas `exp(2πir)`. Il fallait donc envelopper : `chi(n) = exp(2*Pi*I*chareval(G, cc, Mod(n, q)))`.

3. **v7.2d finale** : `Mod(4, 15)` et `Mod(7, 15)` sont des caractères **imprimitifs** (conducteur réel = 5, pas 15). Ils induisent des caractères mod 15 dont les fonctions L ont un facteur d'Euler incorrect en p = 3. Remplacement par les **vrais primitifs** `Mod(14, 15)` et `Mod(8, 15)`.

**Statut après correction** : tous les 8 canaux convergent à la précision machine à σ = 3 (résidus 10⁻⁸ à 10⁻¹⁰). Les paires conjuguées (2, 4) et (6, 8) matchent parfaitement. Script frozen sous le nom `channel_balance_v7_2d.gp`.

**Leçon** : les bibliothèques externes ont des conventions non triviales (chareval retourne r, pas exp(2πir) ; `znconreychar` requiert explicitement G). Les caractères modulaires doivent toujours être vérifiés pour primitivité avant d'être alimentés à une fonction L — la notation `Mod(a, q)` n'implique pas primitivité.

---

### A10 — Réfutation V_eff : le pont géométrique λ = 1/√7 → zéros de ζ (type R + N) — avril 2026

**Sources** :
- `claude.ai/chat/28721eca-8c86-4966-b78c-ccdb4fb05b9b` (6 avril 2026) — pack Thomas
- `claude.ai/chat/5b93b7e5-c0b4-42fd-9b09-17d53bd3a199` (session audit) — exécution et verdict
- `claude.ai/chat/50a62ef8-b009-4eb6-b400-c7c2a8fb5263` — synthèse Phase 4

**Hypothèse testée** : le scaling géométrique brut λ = 1/√7 ≈ 0.3780 capturerait la variance effective des « races de premiers » mod 30 dans le cadre Rubinstein-Sarnak.

**Objet de test — variance effective** :

  V_eff(v̂_C) = Σ_{χ ≠ χ₀} |c_χ|² V(χ)   où   V(χ) = Σ_{γ > 0} 2 / (1/4 + γ²)

**Données mesurées (Thomas, PARI/GP, 200 zéros par caractère)** :

| Caractère | V(χ) |
|---|---|
| ζ (principal, C=9/64) | 0.03908 |
| χ₃ Legendre (C=1/64) | 0.10441 |
| χ₅ Legendre (C=9/64) | 0.14688 |
| χ₅ ordre 4 (C=2/64) | 0.16199 |
| χ₁₅ réel (C=1/64) | 0.44792 |
| χ₁₅ complexe (C=2/64) | [...] |

**Verdict** : le ratio V_eff / (1/7) est **loin de 1** — ce qui signifie que la proximité 3/8 ≈ 1/√7 est une **coïncidence numérique**, pas un mécanisme analytique. L'erreur #23 de la critique externe (Expert) est confirmée.

**Diagnostic théorique** : V(χ) ~ C_RS · log(q_χ). Donc V_eff · dim diverge logarithmiquement. Le bon objet est V_RS = V/log(q) ≈ 0.365, et non V_eff brut.

**Conséquences** :

- « λ = 1/√7 comme invariant universel » est **réfuté dans sa forme actuelle**.
- 1/√7 ≈ 0.378 et 1/φ(30) = 3/8 = 0.375 sont proches mais distincts (écart 0.8%), distinction qui n'est pas un arrondi.
- La structure géométrique sur Δ⁷ et le théorème λ_k = 1/√(k−1) sous isotropie **restent** comme résultat géométrique. Mais leur application arithmétique (isotropie effective des résidus premiers) est conditionnelle à l'hypothèse (P), pas un fait observé.
- Le pont local-global existe via Rubinstein-Sarnak, mais il mène aux **biais de Chebyshev**, pas à RH.

**Leçon** : la confusion entre constante mystique (« 1/√7 ») et objet vérifiable (V_eff, V_RS) est la maturation principale du programme au printemps 2026. Le passage « coïncidence numérique → théorème conditionnel » est une épuration, pas un recul.

---

### A11 — Retrait du plateau B2-v15.2 : `dbm_delta3(L, t_equil)` ignore L (type A + B) — 24 avril 2026 (aujourd'hui)

**Source** : `claude.ai/chat/8eec5b20-fbeb-40c1-8a3f-482cf5a0ffe7` (24 avril 2026, en cours).

**Hypothèse testée** : le plateau `t_equil = −½·ln(6/7) ≈ 0.0770614`, estimé dans le pipeline `lambda_estimator.py` v15.1/15.2 (novembre 2025) avec χ²/dof = 0.93, serait un invariant universel lié à la rigidité spectrale λ² = 1/7 des zéros de ζ.

**Détection du bug** (réexamen aujourd'hui) : le code `rmt_theory.py` du pipeline v15 contient :

```python
def dbm_delta3(L, t_equil):
    lam2 = dbm_lambda_sq(t_equil)
    safe_lam2 = np.clip(lam2, 0.0, 0.9999999)
    return (1.0 / np.pi**2) * np.log(1.0 / (1.0 - safe_lam2)) + 0.44035
```

**L est pris en argument mais jamais utilisé** dans le corps de la fonction. La valeur retournée ne dépend que de `t_equil`. Pour toute valeur de L, `Δ₃_model` est la même constante.

**Conséquence** : le « fit sur Δ₃(L) » de v15.2 ajustait en réalité une **constante** à une **courbe** (Δ₃(L) croît lentement en log L pour les zéros de ζ). Le minimum de χ² existait formellement, donnant `t_equil ≈ 0.077`, mais ce n'était **pas un fit à un modèle physique** — une régression dégénérée.

**Reconstruction correcte (aujourd'hui)** avec le bon Δ₃_GUE(L) = (1/π²)·log(L) + … :

- Les 500 premiers zéros ont `⟨r⟩ = 0.616` (GUE ≈ 0.603), `Δ₃(L=25) ≈ 0.144` (GUE prédit 0.160) — **essentiellement GUE pur**.
- Le modèle d'interpolation linéaire Poisson/GUE avec λ² = 1/7 prédit Δ₃ d'ordre **10× plus grand** que l'empirique → **réfuté**.

**Statut révisé** :

- `t_equil = 0.0770 ± 0.000084` est **un artefact du modèle mal défini**, pas une mesure physique.
- B2-v15.2 est retiré comme mesure de t_equil. L'identité algébrique `t* = −½·log(1 − 1/7) = ½·log(7/6)` reste valide comme **identité géométrique conditionnelle** à λ² = 1/7, mais n'est plus adossée à une mesure empirique.
- Le pont empirique ζ/DBM redevient **conjectural**.

**Leçon** : un fit avec χ²/dof = 0.93 qui paraît excellent peut masquer un bug de spécification du modèle. Le réflexe **réimplémenter depuis la formule théorique et rejouer le test** avant publication est non-négociable. L'auto-audit à 5 mois de distance est le seul remède.

---

### A12 — Candidat C (« torsion KMS mod 30 ») : disqualification par test de spécificité (type N) — 24 avril 2026 (aujourd'hui)

**Source** : `claude.ai/chat/8eec5b20-fbeb-40c1-8a3f-482cf5a0ffe7` (24 avril 2026) ; fichiers `C_minimal_calc.py` et `C_minimal_results.txt` produits dans la même session.

**Hypothèse testée** : il existe une observable sectorielle canonique sur U_M = (ℤ/MℤMℤ)× qui singularise M = 30 et fait apparaître la signature KMS `t* = ½·log(7/6)` comme valeur propre d'un flux modulaire de Bost-Connes restreint.

**Test mis en œuvre** (`C_minimal_calc.py`) : scan des quotients dimensionnels `dim(H_subspace)/dim(H_total)` pour M ∈ {6, 10, 14, 30, 42, 210, 2310}, projetés sur divers stabilisateurs (incluant {1, 11} dans le cas M = 30).

**Résultat** : le ratio `dim(H₀)/dim(H_M) = (φ(M) − 1) / φ(M)` apparaît **mécaniquement** pour chaque M, sans aucune singularité à M = 30. Les observables sectorielles produisent des constantes analogues pour tout module, sans spécificité.

**Verdict doctrinal** (critère d'échec §8 de la note `Algebre_arithmetique_flux_modulaire_30.docx`) : « les variantes mod M produisent des constantes analogues sans spécificité » → **falsifié**. Les branches C3-B et C3-C du candidat C sont fermées.

**Point fin** : même si une observable avait donné **exactement** `Tr(P)/dim H₀ = 6/7`, elle serait disqualifiée comme preuve KMS, parce que la même observable existe mécaniquement pour chaque M par pigeonhole dimensionnel.

**Ce qui reste ouvert** : peut-il exister une observable *non* dimensionnelle qui sélectionne réellement M = 30 ? Candidats pas encore testés :

- invariants spectraux d'un opérateur canonique sur le graphe de Cayley de U₃₀ (pas sur l'espace des fonctions) ;
- transitions de phase KMS d'un vrai système Bost-Connes pour le corps cyclotomique ℚ(ζ₃₀) ;
- observables reliant directement t* à une échelle physique (pas au rapport 6/7).

**Leçon** : un ratio dimensionnel qui coïncide avec une cible attendue est un faux signal s'il apparaît mécaniquement pour des modules voisins. Le **test de spécificité inter-modules** est le garde-fou minimal pour toute conjecture portant sur un invariant modulaire.

---

### A13 — Falsification M3 et trivialité spectrale CRT (type N) — avril 2026

**Sources** :
- `claude.ai/chat/8e3e70ca-5315-49b9-b914-c78dc35adf59` (6 avril 2026) — correction `H4/CRTTransport.lean`
- `claude.ai/chat/3d1701ab-562a-41cf-a05b-33df0e074d21` — session Lean v27.2

**Hypothèse testée** : la relation `L_k · a(k) ≈ Σ 2/γ_n^(2k)` (identification des moments de la tour primoriale aux moments spectraux des zéros de ζ).

**Formule fermée établie** :

  L_k = 2 + (4 + 2·(−1)^k) / 3^k   (exact, prouvé `native_decide`)

**Détection du mismatch** : L_k · a(k) ∼ O(1) quand k croît, alors que Σ 2/γ_n^(2k) ∼ O(14^(−2k)) (décroissance exponentielle en k, puisque γ_1 ≈ 14.13).

**Mismatch structurel** : la tour **ne produit pas** les zéros de ζ. Le transport CRT ajoute des zéros (nouveaux caractères à `c_χ = 0` aux niveaux où un p ∈ TC divise le modulus), pas de structure spectrale non triviale.

**Trivialité spectrale CRT** formalisée : à chaque niveau de la tour primoriale, le spectre de A_TC est

  {ρ ×2, ρ/3 ×4, −ρ/3 ×2, 0 ×(φ(q) − 8)}

où ρ = |TC_lifted|. Les **ratios** entre valeurs propres non-nulles sont invariants par CRT ; la tour est un zoom trivial sur la structure de L3 = 30, pas une extension.

**Conséquences** :

- La conjecture M3 (moments de Hecke → moments spectraux) est **réfutée numériquement**.
- La tour primoriale n'est **pas** un chemin local → global vers les zéros. Elle est une stratification triviale du noyau fini.
- Le passage continu nécessite une injection externe (contenu arithmétique via la distribution des premiers, cf. A5 route N3 Connes adélique).

**Leçon** : vérifier la cohérence d'une identification conjecturée à plusieurs niveaux de la tour **avant** de la promouvoir en structure principale. Un facteur d'échelle qui diverge exponentiellement est un signal décisif.

---

## Partie B — Impasses référencées, à compléter

Pour chaque entrée, je fournis : titre + mention courte + marqueur [À COMPLÉTER] où Couret remplit date, source, énoncé technique, correction, leçon.

### B1 — Cosmologie λ-φ (Phase 0, juillet–septembre 2025)

**Mention** : mentionné dans la chronologie des phases (`claude.ai/chat/50a62ef8-b009-4eb6-b400-c7c2a8fb5263`) comme « élément abandonné » lors du passage aux mathématiques pures.

**À compléter par Couret** :
- Date précise d'abandon : [_____]
- Nature de l'hypothèse λ-φ : [_____]
- Raison de l'abandon (mathématique / physique / doctrinale) : [_____]
- Matériel conservé ou détruit : [_____]
- Leçon : [_____]

---

### B2 — Projet « Factory-432 » (Phase 0, 2025)

**Mention** : listé avec « cosmologie λ-φ » comme abandon Phase 0. Pas d'autres traces dans mes conversations.

**À compléter par Couret** :
- Nature du projet Factory-432 : [_____]
- Lien avec le programme principal : [_____]
- Raison de l'abandon : [_____]
- Date : [_____]
- Leçon : [_____]

---

### B3 — Conjecture λ_n = 1/√(n+1) (Phase 0)

**Mention** : abandonnée au profit de la formulation géométrique λ_k = 1/√(k−1) pour k classes copremières. Pas de détail technique dans mes conversations.

**À compléter par Couret** :
- Énoncé original : [_____]
- Comment la réfutation a émergé : [_____]
- Formulation corrigée et son domaine de validité : [_____]
- Références manuscrits Bernard Couret : [_____]

---

### B4 — Correction L-κ* : σ_c ≈ 0.86

**Mention** : signalée dans mes userMemories comme « L-κ* corrigée, σ_c ≈ 0.86 ». Pas de trace technique précise retrouvée via `conversation_search` (probablement discuté dans un canal parallèle Gemini/GPT).

**À compléter par Couret** :
- Énoncé erroné avant : [_____]
- Mécanisme de détection : [_____]
- Correction et valeur 0.86 : dérivation exacte ? [_____]
- Impact sur la chaîne KLMN : [_____]
- Leçon : [_____]

---

### B5 — Falsification Δ(q) ≠ a·log log q + b (erreur 84.9 %)

**Mention** : listée en Phase 4 (synthèse `claude.ai/chat/50a62ef8-b009-4eb6-b400-c7c2a8fb5263`) comme « Falsification des observables globales primoriales — Δ(q) ≠ a·log log q + b, erreur 84.9 % ». Matérialisée dans `Synthesis/Falsification.lean`.

**À compléter par Couret** :
- Définition exacte de Δ(q) : [_____]
- Jeu de modules q testés : [_____]
- Mesure d'erreur 84.9 % — métrique utilisée : [_____]
- Conséquence pour la tour primoriale au-delà de L4 : [_____]
- Date du rapport Thomas ou du log PARI/GP : [_____]

---

### B6 — Obstruction symplectique J² = −I en dimension impaire

**Mention** : listée en résultats négatifs (`OddDimComplexObstruction.lean`, `SymplecticObstruction.lean`). Argument central : (−1)^n < 0 pour n impair, mais det(J)² ≥ 0, contradiction.

**À compléter par Couret** :
- Énoncé formel complet : [_____]
- Théorèmes Mathlib invoqués : [_____]
- Dimensions impaires concernées dans le programme (|TC| = 3, |V_5| = 5, autres ?) : [_____]
- Conséquence : blocage définitif de quelles heuristiques ? [_____]

---

### B7 — Audit méthodologique Lean 4 : 30 erreurs catégorisées A/B/C/D

**Mention** : 30 erreurs documentées (6 avril 2026, `claude.ai/chat/28721eca-8c86-4966-b78c-ccdb4fb05b9b`). Les items A1–A13 ci-dessus en couvrent probablement 10–15 ; il en reste ~15–20 non détaillés ici.

**À compléter par Couret** :
- Liste intégrale des 30 erreurs (catégories A/B/C/D) : [_____]
- Pour les items **non** déjà couverts en Partie A, énoncé + correction : [_____]
- Registre persistant (fichier `Erreurs_Programme.md` ou similaire) : [_____]

---

### B8 — Overclaims du site web (mars–avril 2026)

**Mention** : badges « certifié Lean 4 », « 0 sorry », « Édition définitive », « Lock 2 dissous » retirés lors de l'audit du 6 avril 2026 et remplacés par « Lean écrit, non compilé », « 1 axiome », « Lock 2 encodé », « Édition audit ». 7 overclaims critiques identifiés et corrigés, sur 3 025 lignes.

**À compléter par Couret** :
- Liste des 7 overclaims : [_____]
- Version du site après correction (URL snapshot) : [_____]
- Politique persistante de contrôle (review pre-publication) : [_____]

---

### B9 — Abandon de la « tour enrichie »

**Mention** : listée comme route éliminée en addition des 5 routes naïves (`claude.ai/chat/3f160154-d615-4008-8e3a-966631ea7b25`). Fait partie des 6 routes fermées mentionnées dans la synthèse (sinc, Connes naïf, Berry-Keating, **tour enrichie**, moments M3, dérive logarithmique).

**À compléter par Couret** :
- Définition opérationnelle de la « tour enrichie » : [_____]
- Tentative précise : [_____]
- Raison du rejet : [_____]
- Différence avec la « tour Hecke » qui reste ouverte : [_____]

---

### B10 — Dérive logarithmique globale falsifiée

**Mention** : route éliminée, mentionnée dans la même synthèse que B9. Évoquée comme « dérive log » globale.

**À compléter par Couret** :
- Énoncé de la dérive log testée : [_____]
- Script de test (PARI/Python) et log : [_____]
- Résultat chiffré de la falsification : [_____]
- Lien avec Δ(q) (entrée B5) ? [_____]

---

### B11 — Anisotropie R = 0.75, direction Couret non-protégée ; d_eff ≈ 5.15

**Mention** : `claude.ai/chat/d69f8c06-7e1c-470a-9cdf-491ec2b9b570` et suite. Résultat : pour atteindre un bruit RS < 0.003 sur λ entre 0.375 et 0.378, il faudrait log N > 110 000, soit N > 10^49000. Inatteignable par ordinateur.

**À compléter par Couret** :
- Définition exacte de R et de d_eff : [_____]
- Script de mesure : [_____]
- Conséquence pour la falsifiabilité de λ = 1/√7 vs 3/8 : [_____]
- Publication séparée possible (d_eff ≈ 5.15 comme résultat propre) : [_____]

---

### B12 — Correction « Parseval L5 = 960 » dans les scripts externes

**Mention** : la correction v28 (entrée A7) a été propagée au pack Lean. Mais d'autres scripts (Python, PARI/GP) ont-ils été corrigés ? Notamment ceux partagés avec Thomas et Expert ?

**À compléter par Couret** :
- Liste des scripts affectés : [_____]
- Scripts déjà corrigés : [_____]
- Scripts restant à auditer : [_____]
- Politique de versionnage : [_____]

---

### B13 — Correction Tesla : bugs κ = 0 et comptage 59 vs 63

**Mention** : bugs identifiés dans le script original Tesla (`claude.ai/chat/e72a745d-87f7-4bca-99f7-2cee93e1a6db`). κ = 0 corrigé en κ = 2 ; comptage 59 corrigé en 63. Séparation des découvertes vérifiées (|K̃₃₀|² peaks, Parseval/φ = 3 étendu, B(1/2,1/2) = π) des métaphores (Schumann × √7, Q-factor, « valve Tesla », β_Tesla = 16/7).

**À compléter par Couret** :
- Script exact et ligne du bug κ = 0 : [_____]
- Origine du comptage 59 (erreur de bord ? erreur d'indice ?) : [_____]
- Version finale Tesla intégrée dans le Master v3 : [_____]
- Politique sur les « métaphores physiques » (exclues du corpus mathématique) : [_____]

---

## Annexe — Chronologie consolidée

| Date | Version | Impasse / correction |
|---|---|---|
| Juil.–sept. 2025 | — | Phase 0. Abandon cosmologie λ-φ, Factory-432, conjecture λ_n = 1/√(n+1) (B1, B2, B3) |
| Oct.–déc. 2025 | v15.1/15.2 | Pipeline DBM, fit t_equil = 0.0770 avec χ²/dof = 0.93 (artefact, cf. A11) |
| Jan.–fév. 2026 | v19 | Stabilisation Lean. 4 axiomes H3, 1 sorry Lemme 7 |
| mars 2026 | v19 → v26 | A1 (spectre TC), A2 (extinctions), A3 (Lock 2 encodé), A4 (Schur v17→v18), B4 (L-κ*) |
| 3 avril 2026 | v26 → v27 | Consolidation ~70 chats, 23→32 fichiers, 4 axiomes H3 → 0. A6 (Lock 2 dissous) |
| 5 avril 2026 | v27.2 | A7 (E = 3 faux à L5), A5 route N5 (µ_k → δ₁ réfutée) |
| 6 avril 2026 | v28 | B7 (30 erreurs), B8 (overclaims), A10 (V_eff réfute λ=1/√7), A13 (M3 falsifié) |
| 7 avril 2026 | v28 → v29/v30 | Mise à jour site + dossier Expert |
| 8 avril 2026 | — | A9 (bug channel_balance v7.2d) |
| 23 avril 2026 | v35.7.2 → v35.8.6 | Refactoring L6Analytic, décomposition spectrale K⊕C⁺⊕C⁻ |
| 24 avril 2026 | v35.8.7 (aujourd'hui) | A11 (B2 plateau retiré), A12 (candidat C réfuté) |

---

## Registre doctrinal

Le fichier Lean `CouretUnification/Meta/RetiredBridges.lean` (proposé dans la session du 24 avril 2026) permet de typer formellement chacune de ces entrées :

```lean
inductive EmpiricalBridgeStatus
  | active          -- A5 routes ouvertes : Connes adélique, Guinand-Weil top-down, Hecke enrichie
  | falsified       -- A10 : λ=1/√7 scaling brut ; A13 : M3
  | retired_artifact -- A11 : B2-v15.2 plateau
  | conjectural     -- DBM mésoscopique : noyau K_t à identifier
  | corrected       -- A4 (v17→v18), A7 (L5 Parseval), A8 (M₄ terminologie), A9 (chareval + imprimitivité)
  | dissolved       -- A3 (Lock 2 encodé), A6 (Lock 2 tautologie Hadamard)
  | eliminated      -- A5 (5 routes), A12 (candidat C), B6 (symplectique), B9 (tour enrichie)
```

Chaque entrée A1–A13 et B1–B13 devrait y apparaître comme une définition typée, avec sa leçon méthodologique attachée.

---

**RHClaimed = false.** La documentation des impasses est la pierre angulaire de cet invariant.
