module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.FourOne
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.OneFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesA
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesB

@[expose] public section



/-! Degree-one/four analog of `StarTwoSideSelf.lean`: linearity of `star1to4`, homogeneity
transport for `star4to1`, and the UNCONDITIONAL "up-then-down" self-identity
`star4to1 (star1to4 β) = (1 / 96) • β` (no alternation hypothesis needed, since `OneCoordinates`
carries no alternation predicate at all), needed for the isometry
`hodgeStarRule_isometry_degree_four`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

/-- `star1to4` is equivariant for real scalars, by unfolding its explicit single-sum definition
and pushing the scalar through `Finset.smul_sum`. -/
theorem star1to4_smul (c : ℝ) (β : OneCoordinates) :
    star1to4 (c • β) = c • star1to4 β := by
  funext i j k l
  show star1to4 (c • β) i j k l = c • star1to4 β i j k l
  unfold star1to4
  simp only [Pi.smul_apply, Finset.smul_sum]
  congr 1
  funext m
  module

/-- `star4to1` preserves homogeneity, mirroring `star3to2_isHomogeneous` one degree up. -/
theorem star4to1_isHomogeneous {n : ℕ} (b : FourCoordinates)
    (hb : ∀ p q r s, (b p q r s).IsHomogeneous n) (i : Fin 5) :
    (star4to1 b i).IsHomogeneous n := by
  show ((1 / 24 : ℝ) • ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5,
      (eps5 i j k l m * tangentWeight j * tangentWeight k * tangentWeight l * tangentWeight m) •
        b j k l m).IsHomogeneous n
  apply (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).smul_mem
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  apply MvPolynomial.IsHomogeneous.sum
  intro l _
  apply MvPolynomial.IsHomogeneous.sum
  intro m _
  exact (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).smul_mem _ (hb j k l m)

end TernaryPeriodPolynomials.Argument.Coercivity
