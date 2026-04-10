import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic

namespace CouretUnification.FunctionalFoundation

abbrev Path (α : Type*) (n : Nat) := Fin (n + 1) → α

namespace Path
variable {α β γ : Type*} {n : Nat}

def start (p : Path α n) : α := p 0
def finish (p : Path α n) : α := p ⟨n, Nat.lt_succ_self n⟩
def HasEndpoints (a b : α) (p : Path α n) : Prop := start p = a ∧ finish p = b
def SameEndpoints (p q : Path α n) : Prop := start p = start q ∧ finish p = finish q

def map (φ : α → β) (p : Path α n) : Path β n := fun i => φ (p i)

@[simp] theorem start_map (φ : α → β) (p : Path α n) : start (map φ p) = φ (start p) := rfl
@[simp] theorem finish_map (φ : α → β) (p : Path α n) : finish (map φ p) = φ (finish p) := rfl
@[simp] theorem map_id (p : Path α n) : map (fun x => x) p = p := by funext i; rfl
@[simp] theorem map_comp (ψ : β → γ) (φ : α → β) (p : Path α n) :
    map ψ (map φ p) = map (ψ ∘ φ) p := by funext i; rfl

theorem sameEndpoints_refl (p : Path α n) : SameEndpoints p p := ⟨rfl, rfl⟩
theorem sameEndpoints_symm {p q : Path α n} : SameEndpoints p q → SameEndpoints q p :=
  fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩

end Path
end CouretUnification.FunctionalFoundation
