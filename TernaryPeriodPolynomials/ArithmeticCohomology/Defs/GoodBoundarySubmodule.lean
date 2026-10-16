module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.DecompositionDefs

@[expose] public section


/-! Elementary closure of actual good-cusp coboundary vanishing. These lemmas
are proved here. -/

noncomputable section
namespace GeneralEisenstein
open Homogeneous

/-- Good-cusp vanishing is a linear condition on the full cohomology quotient. -/
def goodCuspSubmodule (n : ℕ) (χ : RankOneCharacter) (side : Side) :
    Submodule ℂ (StratumH2 n χ side) where
  carrier := {a | VanishesOnGood n χ side a}
  zero_mem' := by
    refine ⟨0, map_zero _, 0, ?_⟩
    intro x q _
    simp
  add_mem' := by
    rintro a b ⟨z, hz, u, hu⟩ ⟨w, hw, v, hv⟩
    refine ⟨z + w, ?_, u + v, ?_⟩
    · rw [map_add, hz, hw]
    · intro x q hq
      change z.val.val x q + w.val.val x q = _
      rw [hu x q hq, hv x q hq, map_add]
      rfl
  smul_mem' := by
    rintro r a ⟨z, hz, u, hu⟩
    refine ⟨r • z, ?_, r • u, ?_⟩
    · rw [map_smul, hz]
    · intro x q hq
      change r • z.val.val x q = _
      rw [hu x q hq, map_smul]
      rfl

/-- Both good-cusp conditions, as a product submodule. -/
def goodBoundarySubmodule (n : ℕ) (χ : RankOneCharacter) :
    Submodule ℂ (BoundaryCoordinates n χ) :=
  (goodCuspSubmodule n χ .plane).prod (goodCuspSubmodule n χ .line)

@[simp] theorem mem_goodBoundarySubmodule (n : ℕ) (χ : RankOneCharacter)
    (b : BoundaryCoordinates n χ) :
    b ∈ goodBoundarySubmodule n χ ↔ GoodBoundaryVanishing n χ b := Iff.rfl

/-- Any operator in the generated algebra preserves the same actual submodule
as its generators. Multiplication of endomorphisms is composition. -/
theorem adjoin_preserves_submodule {V : Type} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ V) (S : Set (Module.End ℂ V))
    (hS : ∀ A ∈ S, ∀ v ∈ W, A v ∈ W)
    (A : Module.End ℂ V) (hA : A ∈ Algebra.adjoin ℂ S) :
    ∀ v ∈ W, A v ∈ W := by
  induction hA using Algebra.adjoin_induction with
  | mem A h => exact hS A h
  | algebraMap r =>
    intro v hv
    change r • v ∈ W
    exact W.smul_mem r hv
  | add A B _ _ hA hB =>
    intro v hv
    exact W.add_mem (hA v hv) (hB v hv)
  | mul A B _ _ hA hB =>
    intro v hv
    exact hA (B v) (hB v hv)

end GeneralEisenstein
end
