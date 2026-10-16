module

public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesRoots
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceEuclideanCoordinates
open SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceParabolicCoordinates

/-- The positive scale coordinate is literally homeomorphic to the real line. -/
def positiveScaleHomeomorph : PositiveScale ≃ₜ ℝ := Real.expOrderIso.toHomeomorph.symm

/-- The five real root coordinates, in the order of the three unipotent and two scale entries. -/
def vectorFiveHomeomorph : ((Fin 3 → ℝ) × (ℝ × ℝ)) ≃ₜ EuclideanSpace ℝ (Fin 5) where
  toFun p := WithLp.toLp 2 ![p.1 0,p.1 1,p.1 2,p.2.1,p.2.2]
  invFun v := (![v 0,v 1,v 2],v 3,v 4)
  left_inv p := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  right_inv v := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  continuous_toFun := (PiLp.continuous_toLp 2 (fun _ : Fin 5 => ℝ)).comp (by fun_prop)
  continuous_invFun := by fun_prop

/-- The actual trace-one positive-form space admits a global Euclidean coordinate homeomorphism. -/
def spaceHomeomorph : Space ≃ₜ EuclideanSpace ℝ (Fin 5) :=
  rootHomeomorph.trans (((Homeomorph.refl (Fin 3 → ℝ)).prodCongr
    (positiveScaleHomeomorph.prodCongr positiveScaleHomeomorph)).trans vectorFiveHomeomorph)

end TernaryPoly.SymmetricSpaceEuclideanCoordinates
