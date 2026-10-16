module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicSwapOpp
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneCosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneCosets

@[expose] public section


/-!
# Arithmetic facts for `τ`-conjugation of good-plane Levi/radical elements

Computations needed for the opposite-edge
("Opp") mirror of `EdgeParabolicAmbientTransport.lean` / `EdgeParabolicLeviFactA.lean`: the general
radical-translation swap identity under `τ`-conjugation (Fact A-opp's arithmetic core), and the
specific `lower 1`-Levi membership fact (Fact A2-opp's arithmetic core).
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (lower)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCosets (icast)
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed)

namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan


/-- **Fact A-opp's arithmetic core**: conjugating a radical good-plane element `Pg c 1 1` by `τ`
swaps the two coordinates of its translation `c`. -/
theorem edgeParabolic_tau_conj_Pg_one (c : ℤ × ℤ) : τ * Pg c 1 1 * τ = Pg (c.2, c.1) 1 1 := by
  have h1 : (kap (1 : binaryArithmeticLevel)) = 1 := map_one kap
  have hPg : ∀ d : ℤ × ℤ, Pg d 1 1 = P (icast d) 1 1 := by
    intro d; rw [Pg]; simp [h1]
  have hSS : (S : GL (Fin 2) ℚ) * S = 1 := by rw [← S_inv]; exact mul_inv_cancel S
  rw [hPg c, hPg (c.2, c.1)]
  show P (0, 0) S 1 * P (icast c) 1 1 * P (0, 0) S 1 = P (icast (c.2, c.1)) 1 1
  rw [P_mul, P_mul]
  simp [bmul, S_val, icast, hSS]

theorem edgeParabolic_kapMat_lower_zero_zero_one :
    (kapMat (lower 1 : binaryArithmeticLevel).val.val) 0 1 = 0 := by
  show 3 * ((lower (1 : ℤ)).val.val 0 1) = 0
  simp [lower]

theorem edgeParabolic_kap_lower_eval_zero_one :
    ((integralEmbed (kap (lower 1)) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = 0 := by
  rw [integralEmbed_kap_val, Matrix.map_apply, edgeParabolic_kapMat_lower_zero_zero_one]
  norm_num

/-- **Fact A2-opp's arithmetic core**: `τ * Pg 0 (lower 1) 1 * τ` lies in
`parabolic .plane ⊓ parabolic .line`. -/
theorem edgeParabolic_tau_conj_Pg_lower_mem :
    τ * Pg (0 : ℤ × ℤ) (lower 1 : binaryArithmeticLevel) 1 * τ ∈
      parabolic .plane ⊓ parabolic .line := by
  have hPg : Pg (0 : ℤ × ℤ) (lower 1 : binaryArithmeticLevel) 1 =
      P (icast (0 : ℤ × ℤ)) (integralEmbed (kap (lower 1))) 1 := by
    rw [Pg]
    simp
  rw [hPg]
  show P (0, 0) S 1 * P (icast (0 : ℤ × ℤ)) (integralEmbed (kap (lower 1))) 1 * P (0, 0) S 1 ∈
    parabolic .plane ⊓ parabolic .line
  rw [P_mul, P_mul]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show InPlaneParabolic _
    constructor <;> simp [P_val]
  · show InLineParabolic _
    unfold InLineParabolic
    rw [P_val]
    constructor
    · simp [Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two,
        S_val, edgeParabolic_kap_lower_eval_zero_one]
    · simp

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
