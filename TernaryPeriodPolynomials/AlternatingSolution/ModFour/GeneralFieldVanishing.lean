module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.AlternatingBridge
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.RationalVanishing

@[expose] public section



/-! Part (c) of `alternating_odd_degree_solution_eq_zero`: a general characteristic-0 field, by reducing to
Part (b) (the rational case) via the base-change equivalence
`TernaryPoly.Paper.alternatingSolution_baseChangeEquiv`. -/

open MvPolynomial TernaryPeriodPolynomials.Argument TernaryPoly.Paper
open scoped TensorProduct

namespace TernaryPeriodPolynomials.Argument.ModFourMain

theorem vanishing_of_odd_alternating_norm_zero_field {F : Type*} [Field F] [CharZero F]
    {n : ℕ} (hn : Odd n) (f : MvPolynomial (Fin 3) F) (hf : f.IsHomogeneous n)
    (halt : IsAlternating f) (hN : threeTermNorm f = 0) : f = 0 := by
  have hQzero : ∀ g : alternatingSolutionSpace ℚ n, g = 0 := by
    intro g
    obtain ⟨hgh, hga, hgn⟩ := (mem_alternatingSolutionSpace_iff g.val n).mp g.2
    exact Subtype.ext (vanishing_of_odd_alternating_norm_zero_rat hn hgh hga hgn)
  have htensor_zero : ∀ x : F ⊗[ℚ] alternatingSolutionSpace ℚ n, x = 0 := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a g => rw [hQzero g]; simp
    | add x y hx hy => rw [hx, hy]; simp
  have hmem : f ∈ alternatingSolutionSpace F n :=
    (mem_alternatingSolutionSpace_iff f n).mpr ⟨hf, halt, hN⟩
  set e := alternatingSolution_baseChangeEquiv F n
  have hx0 : e.symm ⟨f, hmem⟩ = 0 := htensor_zero _
  have hy0 : (⟨f, hmem⟩ : alternatingSolutionSpace F n) = 0 := by
    have h2 := congrArg e hx0
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
  simpa using Subtype.ext_iff.mp hy0

end TernaryPeriodPolynomials.Argument.ModFourMain
