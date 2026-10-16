module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge2

@[expose] public section


/-!
# Levi equivariance of the radical coordinate on cohomology classes

The Levi group `Γ₁'(3) × ℤˣ` acts on `H¹(ℤ², V)` (`SplitRep n`), and the binary coordinate
`Jc : H¹(ℤ², V) → Sym^{n+1}` intertwines this action with `Sym^{n+1} ⊗ det⁻¹` of `κ(m)`
(`Jc_rho`), the factor `ℤˣ` acting trivially.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3a

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2

variable (n : ℕ)

/-- The Levi representation on the radical cohomology. -/
abbrev SplitRep : Rep ℂ Levi := splitRadicalH1Representation goodPlaneSplitting (coefRep n)

/-- **Levi equivariance of the radical coordinate on cohomology classes.** -/
theorem Jh_action (m : binaryArithmeticLevel) (d : ℤˣ)
    (v : groupCohomology.H1 (upperRadicalLatticeRep n)) :
    upperRadicalH1Coordinate n (splitRadicalH1Action goodPlaneSplitting (coefRep n) (m, d) v) =
      Mk n m (upperRadicalH1Coordinate n v) := by
  obtain ⟨ξ, rfl⟩ := oneCocycle_H1_surjective (upperRadicalLatticeRep n) v
  have h1 := splitRadicalH1Action_apply goodPlaneSplitting (coefRep n) (m, d) ξ
  have h2 := upperRadicalH1Coordinate_apply (degree := n)
    (splitRadicalCocycleAction goodPlaneSplitting (coefRep n) (m, d) ξ)
  have h3 := upperRadicalH1Coordinate_apply (degree := n) ξ
  have h4 := coord_levi n ξ m d
  exact (congrArg (fun x => upperRadicalH1Coordinate n x) h1).trans
    (h2.trans (h4.trans (congrArg (fun x => Mk n m x) h3.symm)))

/-- The binary coordinate on the Levi representation `SplitRep n`. -/
def Jc : SplitRep n →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (upperRadicalH1Coordinate n).toLinearMap

theorem Jc_rho (m : binaryArithmeticLevel) (d : ℤˣ) (x : SplitRep n) :
    Jc n ((SplitRep n).ρ (m, d) x) = Mk n m (Jc n x) :=
  Jh_action n m d x

end TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3a
