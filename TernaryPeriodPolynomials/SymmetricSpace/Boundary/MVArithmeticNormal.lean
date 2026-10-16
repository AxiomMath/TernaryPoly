module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVCoordinates
public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticBorel

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBorelCorner SymmetricSpaceGluedArithmetic

/-- Integral action conjugated into a chosen rational frame, as an actual homomorphism. -/
def framedIntegral (a : RationalGL) : IntegralGL →* RealGL :=
  realRational.comp ((MulAut.conj a⁻¹).toMonoidHom.comp integralRational)

@[simp] theorem framedIntegral_apply (a : RationalGL) (g : IntegralGL) :
    framedIntegral a g = realRational (relative a a g) := by
  simp [framedIntegral, relative]

/-- Actual arithmetic stabilizer of both subspaces of the chosen rational full flag. -/
def arithmeticBorel (a : RationalGL) : Subgroup IntegralGL := borelStabilizer.comap (framedIntegral a)

def framedBorel (a : RationalGL) : arithmeticBorel a →* BorelGroup where
  toFun g := ⟨framedIntegral a g.val, g.property⟩
  map_one' := Subtype.ext ((framedIntegral a).map_one)
  map_mul' g h := Subtype.ext ((framedIntegral a).map_mul g.val h.val)

/-- Each diagonal entry is multiplicative on the actual upper-triangular group. -/
def borelDiagonal (i : Fin 3) : BorelGroup →* ℝ where
  toFun g := g.val.val i i
  map_one' := by simp
  map_mul' g h := by
    change (g.val.val * h.val.val) i i = g.val.val i i * h.val.val i i
    rw [matrix_eq_upper g, matrix_eq_upper h]
    fin_cases i <;> simp [upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

def arithmeticDiagonal (a : RationalGL) (i : Fin 3) : arithmeticBorel a →* ℝ :=
  (borelDiagonal i).comp (framedBorel a)

/-- The fixed-frame arithmetic denominator bound controls every power in this subgroup. -/
theorem arithmeticDiagonal_bounded (a : RationalGL) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : arithmeticBorel a) (i : Fin 3), |arithmeticDiagonal a i g| ≤ A := by
  obtain ⟨A, hA, hb⟩ := borel_diagonal_bound a a
  refine ⟨A, hA, fun g i => ?_⟩
  have hm : framedIntegral a g.val ∈ borelStabilizer := g.property
  rw [framedIntegral_apply] at hm
  change |(framedIntegral a g.val).val i i| ≤ A
  rw [framedIntegral_apply]
  exact hb g.val hm i

/-- Boundedness of all powers forces every absolute diagonal entry to be at most one. -/
theorem arithmeticDiagonal_abs_le_one (a : RationalGL) (g : arithmeticBorel a) (i : Fin 3) :
    |arithmeticDiagonal a i g| ≤ 1 := by
  obtain ⟨A, _, hA⟩ := arithmeticDiagonal_bounded a
  by_contra h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt A (lt_of_not_ge h)
  have hb := hA (g ^ n) i
  rw [map_pow, abs_pow] at hb
  exact (not_lt_of_ge hb) hn

/-- Applying the same bound to the inverse forces the absolute diagonal to be exactly one. -/
theorem arithmeticDiagonal_abs_eq_one (a : RationalGL) (g : arithmeticBorel a) (i : Fin 3) :
    |arithmeticDiagonal a i g| = 1 := by
  have hg := arithmeticDiagonal_abs_le_one a g i
  have hi := arithmeticDiagonal_abs_le_one a g⁻¹ i
  have hm : |arithmeticDiagonal a i g| * |arithmeticDiagonal a i g⁻¹| = 1 := by
    rw [←abs_mul, ←map_mul, mul_inv_cancel, map_one, abs_one]
  nlinarith [abs_nonneg (arithmeticDiagonal a i g)]

/-- Both root-scale factors of an arithmetic full-flag stabilizer are literally one. -/
theorem framedBorel_factor1 (a : RationalGL) (g : arithmeticBorel a) :
    factor1 (framedBorel a g) = 1 := by
  change |arithmeticDiagonal a 1 g / arithmeticDiagonal a 0 g| = 1
  rw [abs_div, arithmeticDiagonal_abs_eq_one, arithmeticDiagonal_abs_eq_one, div_self one_ne_zero]

theorem framedBorel_factor2 (a : RationalGL) (g : arithmeticBorel a) :
    factor2 (framedBorel a g) = 1 := by
  change |arithmeticDiagonal a 2 g / arithmeticDiagonal a 1 g| = 1
  rw [abs_div, arithmeticDiagonal_abs_eq_one, arithmeticDiagonal_abs_eq_one, div_self one_ne_zero]

/-- The entire arithmetic Borel action has product form, with unchanged root parameters. -/
theorem framedBorel_extend (a : RationalGL) (g : arithmeticBorel a) (p : Corner) :
    extend (framedBorel a g) p = (shear (framedBorel a g) p.1, p.2) := by
  refine Prod.ext rfl ?_
  apply Prod.ext <;> apply Subtype.ext
  · change factor1 (framedBorel a g) * p.2.1.val = p.2.1.val
    rw [framedBorel_factor1, one_mul]
  · change factor2 (framedBorel a g) * p.2.2.val = p.2.2.val
    rw [framedBorel_factor2, one_mul]

/-- In particular the signed-normal boundary parameter is untouched by arithmetic flag stabilizers. -/
theorem framedBorel_signedAxes (a : RationalGL) (g : arithmeticBorel a) (p : SignedModel) :
    extend (framedBorel a g) (signedAxesHomeomorph p).val =
      (signedAxesHomeomorph (shear (framedBorel a g) p.1, p.2)).val := by
  rw [framedBorel_extend]
  rfl

end TernaryPoly.SymmetricSpaceBoundaryMV
