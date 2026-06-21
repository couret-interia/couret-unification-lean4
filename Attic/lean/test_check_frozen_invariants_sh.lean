-- test_check_frozen_invariants_sh.lean
-- Jeu de test pour check_frozen_invariants.sh v38.4.11
-- Objectif : valider que warn_regex détecte les usages hors commentaires
-- Usage : bash scripts/check_frozen_invariants.sh Attic/lean/test_check_frozen_invariants_sh.lean

-- ════════════════════════════════════════════════════════════
-- vonMangoldt — variations attendues
-- ════════════════════════════════════════════════════════════

-- Cas 1 : usage direct (doit matcher)
def usage_direct : Nat := vonMangoldt

-- Cas 2 : suffixe underscore (doit matcher avec Philosophie B)
def usage_suffix_underscore : Nat := vonMangoldt_something

-- Cas 3 : suffixe alphanumérique (doit matcher avec Philosophie B)
def usage_suffix_alnum : Nat := vonMangoldtValue

-- Cas 4 : définition locale (doit matcher — toute mention est signal)
def vonMangoldt : Nat := 42

-- Cas 5 : double mention sur une ligne (doit matcher 1 ligne)
def double : Nat := vonMangoldt + vonMangoldt_extra

-- ════════════════════════════════════════════════════════════
-- Commentaires — NE doit PAS matcher (le parseur lib les enlève)
-- ════════════════════════════════════════════════════════════

-- Commentaire ligne simple : vonMangoldt évoqué ici, ne doit pas matcher
def faux_match_1 : Nat := 42  -- vonMangoldt mentioned in line comment
def faux_match_2 : Nat := 42  /- vonMangoldt mentioned in block comment -/

/-
  Bloc de commentaire avec vonMangoldt évoqué.
  Ne doit pas matcher non plus.
-/
def faux_match_3 : Nat := 42

-- ════════════════════════════════════════════════════════════
-- digamma — uniquement en ligne def/noncomputable def/structure
-- ════════════════════════════════════════════════════════════

-- Doit matcher (def + identifier digamma)
def digamma : Nat := 42

-- Doit matcher (def + identifier digamma_value)
def digamma_value : Nat := 7

-- Ne doit PAS matcher (usage seul, pas une déclaration def)
def usage_digamma : Nat := digamma

-- Ne doit PAS matcher (commentaire)
def fake_digamma : Nat := 42  -- digamma in comment

-- ════════════════════════════════════════════════════════════
-- zerosInShell — uniquement en ligne def/noncomputable def/structure
-- ════════════════════════════════════════════════════════════

-- Doit matcher
def zerosInShell : List Nat := []

-- Doit matcher (suffixé)
def zerosInShell_value : Nat := 0

-- Ne doit PAS matcher (usage)
def usage_shell : Nat := 42

-- Ne doit PAS matcher (commentaire)
-- zerosInShell : référence en commentaire
