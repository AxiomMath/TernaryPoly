module

public import TernaryPeriodPolynomials.PeriodPolynomial.Apolar.NormSurjective
public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.Dimensions
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodNormMapKernel
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodRationalComparison
public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Zero
public import TernaryPeriodPolynomials.ModularForm.BinaryCuspDimension

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryComplexPeriod
open BinaryFiniteInvariant

/-- Rank-nullity for the actual surjective norm gives the exact rational period dimension. -/
theorem rational_finrank (d : ℕ) (hd : Even d) :
    Module.finrank ℚ (space ℚ d)=(d+2)/4-(d/6+1) := by
  by_cases hz : d=0
  · subst d
    have hzero : ∀ q : space ℚ 0,q=0 := by
      intro q
      apply (rationalEquiv 0).symm.injective
      rw [map_zero]
      exact BinaryModularSymbol.periodSpace_zero_eq _
    simpa using ((finrank_zero_iff_forall_zero (K := ℚ)).mpr hzero)
  · have hn := LinearMap.finrank_range_add_finrank_ker (K := ℚ) (V := oddSymmetric d) (V₂ := invariants d) (normMap d)
    rw [LinearMap.range_eq_top.mpr (BinaryApolar.normMap_surjective d hd (Nat.pos_of_ne_zero hz)),
      finrank_top,invariants_finrank d hd,oddSymmetric_finrank d hd] at hn
    have he := ((kernelEquiv d).trans (rationalEquiv d)).finrank_eq
    rw [←he]
    omega

/-- The exact floor count agrees with the actual full-level cusp dimension convention. -/
theorem period_dimension_arithmetic (d : ℕ) (hd : Even d) :
    (d+2)/4-(d/6+1)=BinaryCuspPeriod.cuspDimension d := by
  have hpar := Nat.even_iff.mp hd
  unfold BinaryCuspPeriod.cuspDimension
  by_cases h : d<10
  · rw [ite_eq_left h]
    omega
  · rw [ite_eq_right h]
    split_ifs with hm
    · change (d-10)%12=2%12 at hm
      omega
    · change ¬(d-10)%12=2%12 at hm
      omega

/-- Rational algebraic period dimension equals the dimension of the actual complex cusp space. -/
theorem rational_finrank_eq_cusp (d : ℕ) (hd : Even d) :
    Module.finrank ℚ (space ℚ d)=Module.finrank ℂ (BinaryCuspPeriod.Forms d) := by
  rw [rational_finrank d hd,period_dimension_arithmetic d hd,BinaryCuspPeriod.forms_finrank d hd]

end TernaryPoly.BinaryComplexPeriod
