module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneModel
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IdentityPlaneRestriction

@[expose] public section


/-!
# Every good-plane class has zero restriction to the radical

The element `z = diag(1, 1, -1)` of the good-plane stabilizer `Λ` inverts the radical lattice
(`z⁻¹ u(b) z = u(-b)`) and acts on the restriction of the coefficients to the plane `X₂ = 0` by
`-1` (`res_DK`). Exactly as for the identity plane with the Levi element `-I₂` (where odd degree
was needed), the alternation of the restriction of any two-cocycle to the radical vanishes, so the
restriction map `H²(Λ, V) → H²(ℤ², V)` is zero in every positive degree
(`goodPlaneH2_restriction_zero`). Hence the Hochschild–Serre edge of `GoodPlaneModel` is defined on
all of `H²(Λ, V)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneRestriction

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel

variable (n : ℕ)

theorem inl_eq : goodPlaneExtension.inl = radInc := rfl

theorem DK_mul_self : DK * DK = 1 := by
  have h : DK * DK = Gel (0 + act 1 (-1) 0) (1 * 1) ((-1) * (-1)) := Gel_mul 0 0 1 1 (-1) (-1)
  have h1 : (0 : ℤ × ℤ) + act 1 (-1) 0 = 0 := by rw [act_zero, add_zero]
  have h2 : (1 : binaryArithmeticLevel) * 1 = 1 := mul_one 1
  have h3 : ((-1 : ℤˣ) * (-1)) = 1 := Int.units_mul_self _
  rw [h, h1, h2, h3, Gel_one]

theorem DK_inv : DK⁻¹ = DK := inv_eq_of_mul_eq_one_right DK_mul_self

theorem conj_DK (b : RadicalLattice) :
    DK⁻¹ * goodPlaneExtension.inl b * DK = goodPlaneExtension.inl b⁻¹ := by
  rw [DK_inv, inl_eq, radInc_eq, radInc_eq]
  have h : DK * Gel b.toAdd 1 1 * DK =
      Gel (0 + act 1 (-1) b.toAdd + act (1 * 1) ((-1) * 1) 0) (1 * 1 * 1) ((-1) * 1 * (-1)) := by
    rw [DK, Gel_mul, Gel_mul]
  have e1 : 0 + act 1 (-1) b.toAdd + act (1 * 1) ((-1) * 1) 0 = (b⁻¹).toAdd := by
    rw [act_zero, act_one, add_zero, zero_add, toAdd_inv]
    simp
  have e2 : (1 : binaryArithmeticLevel) * 1 * 1 = 1 := by rw [mul_one, mul_one]
  have e3 : ((-1 : ℤˣ) * 1 * (-1)) = 1 := by
    rw [mul_one]
    exact Int.units_mul_self _
  rw [h, e1, e2, e3]

theorem res_DK (v : HomogeneousPoly n) :
    binaryHomogeneousRestrict n ((coefRep n).ρ DK v) = -binaryHomogeneousRestrict n v := by
  change IdentityPlaneCoordinate.res n
    (IdentityPlaneCoordinate.ρn n (Pg 0 1 (-1)) v) = _
  have hB : integralEmbed (kap (1 : binaryArithmeticLevel)) = 1 := by simp
  have h1 : ((uq (-1) : ℚˣ) : ℚ) = -1 := by
    rw [uq_val]
    simp
  have h2 : (((-1 : ℚ) : ℂ))⁻¹ = -1 := by norm_num
  unfold Pg
  rw [IdentityPlaneCoordinate.restrict_P, hB, IdentityPlaneCoordinate.Abin_one, h1, h2]
  exact neg_one_smul ℂ (IdentityPlaneCoordinate.res n v)

/-- **Every class of `H²(Λ, V)` restricts to zero on the radical lattice** (`n > 0`). -/
theorem goodPlaneH2_restriction_zero (hn : 0 < n) (x : groupCohomology.H2 (coefRep n)) :
    twoCohomologyRestriction goodPlaneExtension.inl (coefRep n) x = 0 := by
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective (coefRep n) x
  rw [twoCohomologyRestriction_apply]
  apply (upperRadicalTwoCocycle_H2_zero_iff n hn
    (twoCocycleRestriction goodPlaneExtension.inl (coefRep n) cycle)).mpr
  exact twoCocycle_projected_alternation_zero goodPlaneExtension.inl (coefRep n)
    (binaryHomogeneousRestrict n) (binaryHomogeneousRestrict_upperLattice n) DK (conj_DK)
    (res_DK n) cycle radicalLatticeFirst radicalLatticeSecond

end TernaryPeriodPolynomials.LevelThree.GoodPlaneRestriction
