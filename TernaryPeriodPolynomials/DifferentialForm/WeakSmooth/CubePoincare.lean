module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Weak.OnePoincare

@[expose] public section


/-! Actual weak one-form Poincare exactness on the five-dimensional product test box. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth

abbrev WeakCubeZero := Fin 0 → ℝ
abbrev WeakCubeOne := WeakCubeZero × ℝ
abbrev WeakCubeTwo := WeakCubeOne × ℝ
abbrev WeakCubeThree := WeakCubeTwo × ℝ
abbrev WeakCubeFour := WeakCubeThree × ℝ
abbrev WeakCubeFive := WeakCubeFour × ℝ

def testCubeDomainZero : TopologicalSpace.Opens WeakCubeZero := ⊤
def testCubeDomainOne : TopologicalSpace.Opens WeakCubeOne := testCylinder testCubeDomainZero
def testCubeDomainTwo : TopologicalSpace.Opens WeakCubeTwo := testCylinder testCubeDomainOne
def testCubeDomainThree : TopologicalSpace.Opens WeakCubeThree := testCylinder testCubeDomainTwo
def testCubeDomainFour : TopologicalSpace.Opens WeakCubeFour := testCylinder testCubeDomainThree
def testCubeDomainFive : TopologicalSpace.Opens WeakCubeFive := testCylinder testCubeDomainFour

/-- There are no positive-degree directions on the actual zero-dimensional test box. -/
theorem testCubeDomainZero_weakOneExact : ScalarWeakOneExact testCubeDomainZero :=
  scalarWeakOneExact_of_subsingleton testCubeDomainZero

theorem testCubeDomainOne_weakOneExact : ScalarWeakOneExact testCubeDomainOne :=
  scalarWeakOneExact_cylinder testCubeDomainZero testCubeDomainZero_weakOneExact

theorem testCubeDomainTwo_weakOneExact : ScalarWeakOneExact testCubeDomainTwo :=
  scalarWeakOneExact_cylinder testCubeDomainOne testCubeDomainOne_weakOneExact

theorem testCubeDomainThree_weakOneExact : ScalarWeakOneExact testCubeDomainThree :=
  scalarWeakOneExact_cylinder testCubeDomainTwo testCubeDomainTwo_weakOneExact

theorem testCubeDomainFour_weakOneExact : ScalarWeakOneExact testCubeDomainFour :=
  scalarWeakOneExact_cylinder testCubeDomainThree testCubeDomainThree_weakOneExact

/-- Every actual closed algebraic-current one-form on the genuine five-dimensional product box
has an actual scalar-current primitive, without any continuity or smoothing hypothesis. -/
theorem testCubeDomainFive_weakOneExact : ScalarWeakOneExact testCubeDomainFive :=
  scalarWeakOneExact_cylinder testCubeDomainFour testCubeDomainFour_weakOneExact

end TernaryPoly.PolynomialFormWeakSmooth
