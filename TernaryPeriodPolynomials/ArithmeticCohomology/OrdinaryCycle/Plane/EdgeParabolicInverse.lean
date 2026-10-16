module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Plane.EdgeParabolic

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.OrdinaryPlaneEdge
open OrdinaryResidueParabolic

/-- The inverse actual block matrix retains the inverse Levi and inverse normal scalars. -/
theorem inverse_block (g : OrdinaryFullAction.GL3) (lam : ℚˣ) (u : Fin 2 → ℚ)
    (C : BinaryModularSymbol.GL2) (hg : g.val = blockMatrix lam u C) :
    (g⁻¹).val = blockMatrix lam⁻¹ (fun i => (g⁻¹).val i.succ 0) C⁻¹ := by
  have hb (i j : Fin 2) : (g⁻¹).val i.succ j.succ = (C⁻¹).val i j :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M i j) (inverse_lowerBlock g lam u C hg)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blockMatrix] using inverse_first_row g lam u C hg 0
  · exact inverse_first_row g lam u C hg 1
  · exact inverse_first_row g lam u C hg 2
  · rfl
  · exact hb 0 0
  · exact hb 0 1
  · rfl
  · exact hb 1 0
  · exact hb 1 1

/-- The actual inverse coefficient-and-cycle convention projects to inverse binary action on symbols. -/
theorem binaryProject_inverse_action_binaryCone (g : OrdinaryFullAction.GL3) (lam : ℚˣ) (u : Fin 2 → ℚ)
    (C : BinaryModularSymbol.GL2) (hg : g.val = blockMatrix lam u C) (c : BinaryModularSymbol.St) :
    binaryProject (OrdinaryFullAction.cycleAction g⁻¹ (binaryCone c)) = BinaryModularSymbol.action C⁻¹ c :=
  binaryProject_action_binaryCone g⁻¹ lam⁻¹ (fun i => (g⁻¹).val i.succ 0) C⁻¹
    (inverse_block g lam u C hg) c

end TernaryPoly.OrdinaryPlaneEdge
