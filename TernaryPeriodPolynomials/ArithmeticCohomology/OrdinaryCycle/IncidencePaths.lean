module

public import TernaryPeriodPolynomials.Building.BipartitePathChains
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryIncidencePaths
open BipartitePathChains
variable {L P : Type*}

/-- Total coefficient of an actual finite vertex chain. -/
def augmentation : Chain₀ L P →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ (fun _ => 1)

@[simp] theorem augmentation_single (v : Vertex L P) (q : ℚ) :
    augmentation (Finsupp.single v q) = q := by
  simp [augmentation,Finsupp.linearCombination_single]

theorem augmentation_boundary (r : L → P → Prop) (c : Chain₁ r) :
    augmentation (boundary r c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd,add_zero]
  | single e q => simp only [boundary_single,map_sub,augmentation_single,sub_self]

/-- Finite linear extension of actual path chains from a specified base vertex. -/
def pathLift (r : L → P → Prop) (hc : (graph r).Preconnected) (base : Vertex L P) :
    Chain₀ L P →ₗ[ℚ] Chain₁ r :=
  Finsupp.linearCombination ℚ (chosenPathChain r hc base)

theorem boundary_pathLift (r : L → P → Prop) (hc : (graph r).Preconnected)
    (base : Vertex L P) (c : Chain₀ L P) :
    boundary r (pathLift r hc base c) = c - augmentation c • Finsupp.single base 1 := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero,zero_smul,sub_zero]
  | add c d hc hd => simp only [map_add,hc,hd,add_smul]; abel
  | single v q =>
    simp only [pathLift,Finsupp.linearCombination_single,map_smul,boundary_chosenPathChain,
      augmentation_single,smul_sub,Finsupp.smul_single,smul_eq_mul,mul_one]

theorem zero_augmentation_filling (r : L → P → Prop) (hc : (graph r).Preconnected)
    (base : Vertex L P) (c : Chain₀ L P) (h : augmentation c = 0) :
    ∃ b, boundary r b = c := by
  exact ⟨pathLift r hc base c,by rw [boundary_pathLift,h,zero_smul,sub_zero]⟩

end TernaryPoly.OrdinaryIncidencePaths
