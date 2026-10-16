module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.BadEdgeOrbit

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem rational_pair_integral_reduce (first second : ℚ) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧ (c : ℚ) * first + (d : ℚ) * second = 0 := by
  by_cases first_zero : first = 0
  · exact ⟨0, -1, 1, 0, by norm_num, by simp [first_zero]⟩
  · let ratio := second / first
    obtain ⟨u, v, bezout⟩ := Rat.isCoprime_num_den ratio
    refine ⟨v, u, -ratio.num, ratio.den, ?_, ?_⟩
    · nlinarith [bezout]
    · have denominator_nonzero : (ratio.den : ℚ) ≠ 0 := by exact_mod_cast ratio.den_nz
      have ratio_eq := Rat.num_div_den ratio
      change (ratio.num : ℚ) / (ratio.den : ℚ) = second / first at ratio_eq
      have relation := (div_eq_div_iff denominator_nonzero first_zero).mp ratio_eq
      push_cast
      nlinarith [relation]

def integralPairRows01 (a b c d : ℤ) (determinant : a * d - b * c = 1) : IntegralGL3 :=
  ⟨!![a,b,0;c,d,0;0,0,1], !![d,-b,0;-c,a,0;0,0,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [determinant], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [determinant]⟩

def integralPairRows02 (a b c d : ℤ) (determinant : a * d - b * c = 1) : IntegralGL3 :=
  ⟨!![a,0,b;0,1,0;c,0,d], !![d,0,-b;0,1,0;-c,0,a], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [determinant], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [determinant]⟩

def integralPairRows12 (a b c d : ℤ) (determinant : a * d - b * c = 1) : IntegralGL3 :=
  ⟨!![1,0,0;0,a,b;0,c,d], !![1,0,0;0,d,-b;0,-c,a], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [determinant], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [determinant]⟩

theorem rational_matrix_integral_upper_reduce (matrix : RationalGL3) :
    ∃ integral : IntegralGL3, GeneralLinearGroup.map (Int.castRingHom ℚ) integral * matrix ∈
      parabolic .plane ⊓ parabolic .line := by
  obtain ⟨a, b, c, d, determinant, eliminates⟩ :=
    rational_pair_integral_reduce (matrix.val 0 0) (matrix.val 1 0)
  let first := integralPairRows01 a b c d determinant
  let step_one := GeneralLinearGroup.map (Int.castRingHom ℚ) first * matrix
  have first_zero : step_one.val 1 0 = 0 := by
    simpa [step_one, first, integralPairRows01, Matrix.mul_apply, Fin.sum_univ_three]
      using eliminates
  obtain ⟨a', b', c', d', determinant', eliminates'⟩ :=
    rational_pair_integral_reduce (step_one.val 0 0) (step_one.val 2 0)
  let second := integralPairRows02 a' b' c' d' determinant'
  let step_two := GeneralLinearGroup.map (Int.castRingHom ℚ) second * step_one
  have second_zero : step_two.val 2 0 = 0 := by
    simpa [step_two, second, integralPairRows02, Matrix.mul_apply, Fin.sum_univ_three]
      using eliminates'
  have first_preserved : step_two.val 1 0 = 0 := by
    simpa [step_two, second, integralPairRows02, Matrix.mul_apply, Fin.sum_univ_three]
      using first_zero
  obtain ⟨a'', b'', c'', d'', determinant'', eliminates''⟩ :=
    rational_pair_integral_reduce (step_two.val 1 1) (step_two.val 2 1)
  let third := integralPairRows12 a'' b'' c'' d'' determinant''
  let step_three := GeneralLinearGroup.map (Int.castRingHom ℚ) third * step_two
  have third_zero : step_three.val 2 1 = 0 := by
    simpa [step_three, third, integralPairRows12, Matrix.mul_apply, Fin.sum_univ_three]
      using eliminates''
  have final_first : step_three.val 1 0 = 0 := by
    simp [step_three, third, integralPairRows12, Matrix.mul_apply, Fin.sum_univ_three,
      first_preserved, second_zero]
  have final_second : step_three.val 2 0 = 0 := by
    simp [step_three, third, integralPairRows12, Matrix.mul_apply, Fin.sum_univ_three,
      first_preserved, second_zero]
  refine ⟨third * second * first, ?_⟩
  have product : GeneralLinearGroup.map (Int.castRingHom ℚ) (third * second * first) * matrix =
      step_three := by simp only [step_three, step_two, step_one, map_mul, mul_assoc]
  rw [product]
  exact ⟨⟨final_second, third_zero⟩, ⟨final_first, final_second⟩⟩

theorem integral_edge_frames (edge : Edges) :
    ∃ frame : IntegralGL3,
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) frame) : Edges) = edge := by
  induction edge using Quotient.inductionOn with
  | _ matrix =>
    obtain ⟨integral, upper⟩ := rational_matrix_integral_upper_reduce matrix
    refine ⟨integral⁻¹, ?_⟩
    apply QuotientGroup.eq.mpr
    simpa only [map_inv, inv_inv] using upper

theorem building_edge_orbits (edge : Edges) :
    GoodFlag .plane (endpoint .plane edge) ∨ GoodFlag .line (endpoint .line edge) ∨
      ∃ matrix : rationalLevel, matrix.val • standardBadEdge = edge :=
  edge_orbits_of_integral_frames integral_edge_frames edge

theorem pathCocycle_innerBoundary {degree : ℕ} (degree_positive : 0 < degree)
    {polynomial : HomogeneousPoly degree} (solution : SymmetricSolution polynomial)
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional) :
    InnerBoundary degree trivialCharacter .line
      (globalCoordinates degree trivialCharacter
        (pathCocycle functional_property specialPaths_isPathFamily)).2 :=
  pathCocycle_inner_of_bad_edge_orbit building_edge_orbits degree_positive solution functional_property

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
