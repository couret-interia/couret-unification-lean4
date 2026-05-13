/-
  Couret–Unification
  Logic/C2/Window.lean

  Contexte destinataire : préparé pour relecture mathématique externe.

  Doctrine : A rend le calcul fini ; λ calibre la discernabilité.
  Statut : [M] scaffold typé sans sorry.
  Noyau local : [D] preuve du support compact du cutoff de Fejer côté Fourier.

  Raison d'exister :
  typer et fermer la condition de fenêtre compacte côté Fourier nécessaire
  avant toute acceptation d'un observable C2 concret.

  Garde-fous :
  * Aucune revendication RH.
  * Aucune revendication Hilbert–Pólya.
  * Aucune borne empirique C2 n'est prouvée ici.
  * Ce fichier prouve seulement que le cutoff de type Fejer côté Fourier
    possède un support compact.

  Séparation des seuils :
  * A est le cutoff de bande finie : il rend finie la trace arithmétique
    de Guinand–Weil.
  * λ = 1/sqrt(7) est la calibration de discernabilité sur Δ⁷.
  * Ne pas confondre ces deux seuils.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

noncomputable section

namespace CouretUnification.Logic.C2

/-!
## 0. Fenêtre de Paley–Wiener côté Fourier

La première exigence froide de la phase de refroidissement n'est pas encore
un observable concret. C'est la condition de support compact côté Fourier.

Dans la formule explicite de Guinand–Weil, le côté arithmétique contient
des termes de la forme

  sum_{p,m} (log p) / p^(m/2) * hhat (m * log p).

Si `hhat` a un support compact dans `[-A,A]`, alors seuls les termes tels que

  m * log p <= A

survivent, ce qui équivaut à

  p^m <= exp A.

Ce fichier stocke directement l'objet côté Fourier. Nous ne nous engageons
volontairement pas ici sur une API Mathlib concrète de transformée de Fourier.
Un fichier analytique ultérieur pourra relier `hhat` à une vraie fonction
test `h`.
-/

/--
Une fenêtre compacte côté Fourier de type Paley–Wiener.

Nous nous limitons aux fenêtres réelles côté Fourier, car la doctrine C2
utilise des cutoffs pairs, réels et positifs de type triangulaire/Fejer.
Un futur module pourra généraliser aux fenêtres complexes si des tests
asymétriques deviennent nécessaires.
-/
structure PaleyWienerWindow where
  /-- Rayon du support compact côté Fourier. -/
  A : ℝ
  /-- Le rayon de support est strictement positif. -/
  A_pos : 0 < A
  /-- Fenêtre test côté Fourier. -/
  hhat : ℝ → ℝ
  /-- Support compact côté Fourier. -/
  support_bound : ∀ x : ℝ, A < |x| → hhat x = 0

namespace PaleyWienerWindow

/-- Reformulation du support compact : hors de la bande déclarée,
    la fenêtre s'annule. -/
theorem vanish_outside (w : PaleyWienerWindow) (x : ℝ) (hx : w.A < |x|) :
    w.hhat x = 0 := by
  exact w.support_bound x hx

end PaleyWienerWindow

/-!
## 1. Fenêtre triangulaire côté Fourier de type Fejer

Le modèle concret est la fenêtre triangulaire compacte

  hhat_A(x) = max 0 (1 - |x| / A).

C'est le cutoff côté Fourier de type Fejer utilisé par C2 :
compact, positif et de bande finie par construction.
-/

/-- Cutoff triangulaire compact côté Fourier de type Fejer. -/
def fejerHat (A x : ℝ) : ℝ :=
  max 0 (1 - |x| / A)

/-- Fermeture du support pour le cutoff triangulaire de type Fejer. -/
theorem fejerHat_support_bound (A : ℝ) (hA : 0 < A) :
    ∀ x : ℝ, A < |x| → fejerHat A x = 0 := by
  intro x hx
  unfold fejerHat
  have h1 : 1 < |x| / A := by
    rw [lt_div_iff₀ hA]
    linarith
  have h2 : 1 - |x| / A < 0 := by
    linarith
  exact max_eq_left (le_of_lt h2)

/-- Fenêtre de Paley–Wiener de type Fejer, de rayon `A`. -/
def fejerWindow (A : ℝ) (hA : 0 < A) : PaleyWienerWindow where
  A := A
  A_pos := hA
  hhat := fejerHat A
  support_bound := fejerHat_support_bound A hA

/-!
## 2. Prédicat de finitude arithmétique

C'est le pont froid entre le support compact côté Fourier et la trace
arithmétique finie.

Nous n'implémentons pas encore ici les nombres premiers ni les poids de
von Mangoldt. Nous typons seulement le prédicat exprimant qu'une fréquence
logarithmique `y` se trouve dans la bande de support.
-/

/-- Une fréquence logarithmique appartient à la bande de Fourier déclarée. -/
def InsideBand (w : PaleyWienerWindow) (y : ℝ) : Prop :=
  |y| ≤ w.A

/--
Si la fenêtre côté Fourier est non nulle en `y`, alors `y` appartient
nécessairement à la bande compacte déclarée.
-/
theorem hhat_ne_zero_implies_insideBand
    (w : PaleyWienerWindow) (y : ℝ)
    (hy : w.hhat y ≠ 0) : InsideBand w y := by
  unfold InsideBand
  by_contra h
  push Not at h
  exact hy (w.support_bound y h)

/-!
## 3. Note de transition C2

Le prochain fichier pourra définir un observable concret seulement après
avoir choisi comment la trace arithmétique finie produite par `w.hhat`
est normalisée dans Δ⁷.

Ordre :

1. Contrat compact côté Fourier `PaleyWienerWindow`.          -- ce fichier
2. Preuve concrète du support de Fejer.                       -- fermé ici
3. Première instance d'observable.                            -- prochain scaffold
4. Fournisseur concret depuis les données mod 30 vers Δ⁷.     -- plus tard

Statut doctrinal :

* Le scaffold global reste `[M]`.
* La preuve locale du support compact de `fejerHat` est `[D]`.
* Aucun énoncé C2 empirique, spectral ou analytique global n'est prouvé ici.
-/

end CouretUnification.Logic.C2
