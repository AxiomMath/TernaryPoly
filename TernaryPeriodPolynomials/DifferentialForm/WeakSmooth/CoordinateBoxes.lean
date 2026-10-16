module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.AffineExactness
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CubeMass
public import TernaryPeriodPolynomials.SymmetricSpace.ChartsBasic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-! Actual weak-current exactness on affine boxes in the genuine five-coordinate chart model. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open SymmetricSpaceCharts

/-- A fixed continuous linear identification of the genuine five-dimensional product model
with the actual coordinate space of the symmetric space. -/
def weakCubeCoordinateEquiv : WeakCubeFive ≃L[ℝ] Coordinates :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp only [WeakCubeFive, WeakCubeFour, WeakCubeThree, WeakCubeTwo, WeakCubeOne,
      WeakCubeZero, Coordinates, Module.finrank_prod, Module.finrank_fin_fun,
      Module.finrank_self])

/-- An actual affine box, defined by the inverse image under its genuine affine coordinate map. -/
def coordinateTestBox (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates) :
    TopologicalSpace.Opens Coordinates :=
  transportedTestDomain (affineTestHomeomorph e a) testCubeDomainFive

/-- Every actual closed weak one-form on an affine coordinate box has an actual scalar weak
primitive. This statement concerns the literal compact smooth test dual. -/
theorem coordinateTestBox_weakOneExact (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates) :
    ScalarWeakOneExact (coordinateTestBox e a) :=
  scalarWeakOneExact_affine e a testCubeDomainFive testCubeDomainFive_weakOneExact

/-- The actual transported iterated-integral mass. Its geometric Jacobian normalization is
kept separate from this literal affine test-dual definition. -/
def coordinateTestBoxMass (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates) :
    ScalarWeak (coordinateTestBox e a) :=
  scalarWeakAffineEquiv e a testCubeDomainFive weakCubeMassFive

theorem coordinateTestBoxMass_rigid (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates) :
    ScalarWeakZeroRigid (coordinateTestBox e a) (coordinateTestBoxMass e a) :=
  scalarWeakZeroRigid_affine e a testCubeDomainFive weakCubeMassFive weakCubeMassFive_rigid

theorem coordinateTestBoxMass_closed (e : WeakCubeFive ≃L[ℝ] Coordinates) (a : Coordinates) :
    HasZeroWeakDerivative (coordinateTestBox e a) (coordinateTestBoxMass e a) := by
  intro v
  obtain ⟨w, rfl⟩ := e.surjective v
  change scalarWeakDerivative _ (e w) (scalarWeakAffineEquiv e a _ weakCubeMassFive) = 0
  rw [scalarWeakAffineEquiv_derivative, weakCubeMassFive_closed, map_zero]

/-- Exact zero-gradient characterization on actual coordinate boxes. -/
theorem coordinateTestBox_zeroGradient_iff (e : WeakCubeFive ≃L[ℝ] Coordinates)
    (a : Coordinates) (T : ScalarWeak (coordinateTestBox e a)) :
    HasZeroWeakDerivative (coordinateTestBox e a) T ↔ ∃ c : ℝ, T = c • coordinateTestBoxMass e a := by
  constructor
  · exact coordinateTestBoxMass_rigid e a T
  · rintro ⟨c, rfl⟩ v
    rw [map_smul, coordinateTestBoxMass_closed, smul_zero]

end TernaryPoly.PolynomialFormWeakSmooth
