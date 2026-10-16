module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CubePoincare
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Weak.Zero

@[expose] public section


/-! Actual iterated-integral mass currents and zero-gradient rigidity on the five-dimensional box. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set
open scoped Distributions

/-- The actual unit compact test on the zero-dimensional base. -/
def cubeZeroUnitTest : 𝓓(testCubeDomainZero, ℝ) where
  toFun _ := 1
  contDiff' := contDiff_const
  hasCompactSupport' := isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)
  tsupport_subset' := subset_univ _

/-- Actual zero-dimensional test integration is evaluation at the unique base point. -/
def weakCubeMassZero : ScalarWeak testCubeDomainZero where
  toFun f := f 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def weakCubeMassOne : ScalarWeak testCubeDomainOne := weakFiberLift testCubeDomainZero weakCubeMassZero
def weakCubeMassTwo : ScalarWeak testCubeDomainTwo := weakFiberLift testCubeDomainOne weakCubeMassOne
def weakCubeMassThree : ScalarWeak testCubeDomainThree := weakFiberLift testCubeDomainTwo weakCubeMassTwo
def weakCubeMassFour : ScalarWeak testCubeDomainFour := weakFiberLift testCubeDomainThree weakCubeMassThree
def weakCubeMassFive : ScalarWeak testCubeDomainFive := weakFiberLift testCubeDomainFour weakCubeMassFour

theorem weakCubeMassZero_rigid : ScalarWeakZeroRigid testCubeDomainZero weakCubeMassZero := by
  intro T _
  refine ⟨T cubeZeroUnitTest, ?_⟩
  apply LinearMap.ext
  intro f
  have hf : f = f 0 • cubeZeroUnitTest := by
    apply TestFunction.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    change f x = f 0 * 1
    rw [hx, mul_one]
  change T f = T cubeZeroUnitTest * f 0
  calc
    T f = T (f 0 • cubeZeroUnitTest) := congrArg T hf
    _ = T cubeZeroUnitTest * f 0 := by rw [map_smul]; exact mul_comm _ _

theorem weakCubeMassOne_rigid : ScalarWeakZeroRigid testCubeDomainOne weakCubeMassOne :=
  scalarWeakZeroRigid_cylinder testCubeDomainZero weakCubeMassZero weakCubeMassZero_rigid

theorem weakCubeMassTwo_rigid : ScalarWeakZeroRigid testCubeDomainTwo weakCubeMassTwo :=
  scalarWeakZeroRigid_cylinder testCubeDomainOne weakCubeMassOne weakCubeMassOne_rigid

theorem weakCubeMassThree_rigid : ScalarWeakZeroRigid testCubeDomainThree weakCubeMassThree :=
  scalarWeakZeroRigid_cylinder testCubeDomainTwo weakCubeMassTwo weakCubeMassTwo_rigid

theorem weakCubeMassFour_rigid : ScalarWeakZeroRigid testCubeDomainFour weakCubeMassFour :=
  scalarWeakZeroRigid_cylinder testCubeDomainThree weakCubeMassThree weakCubeMassThree_rigid

/-- Every actual zero-gradient current on the genuine five-dimensional product box is a
scalar multiple of its actual iterated-integral mass current. -/
theorem weakCubeMassFive_rigid : ScalarWeakZeroRigid testCubeDomainFive weakCubeMassFive :=
  scalarWeakZeroRigid_cylinder testCubeDomainFour weakCubeMassFour weakCubeMassFour_rigid


theorem weakCubeMassZero_closed : HasZeroWeakDerivative testCubeDomainZero weakCubeMassZero := by
  intro v
  change scalarWeakGradient testCubeDomainZero weakCubeMassZero v = 0
  have hv : v = 0 := Subsingleton.elim _ _
  rw [hv, map_zero]

theorem weakCubeMassOne_closed : HasZeroWeakDerivative testCubeDomainOne weakCubeMassOne :=
  weakFiberLift_hasZeroWeakDerivative testCubeDomainZero weakCubeMassZero weakCubeMassZero_closed

theorem weakCubeMassTwo_closed : HasZeroWeakDerivative testCubeDomainTwo weakCubeMassTwo :=
  weakFiberLift_hasZeroWeakDerivative testCubeDomainOne weakCubeMassOne weakCubeMassOne_closed

theorem weakCubeMassThree_closed : HasZeroWeakDerivative testCubeDomainThree weakCubeMassThree :=
  weakFiberLift_hasZeroWeakDerivative testCubeDomainTwo weakCubeMassTwo weakCubeMassTwo_closed

theorem weakCubeMassFour_closed : HasZeroWeakDerivative testCubeDomainFour weakCubeMassFour :=
  weakFiberLift_hasZeroWeakDerivative testCubeDomainThree weakCubeMassThree weakCubeMassThree_closed

theorem weakCubeMassFive_closed : HasZeroWeakDerivative testCubeDomainFive weakCubeMassFive :=
  weakFiberLift_hasZeroWeakDerivative testCubeDomainFour weakCubeMassFour weakCubeMassFour_closed

/-- Exact characterization of zero-gradient algebraic currents on the actual five-dimensional box. -/
theorem testCubeDomainFive_zeroGradient_iff (T : ScalarWeak testCubeDomainFive) :
    HasZeroWeakDerivative testCubeDomainFive T ↔ ∃ c : ℝ, T = c • weakCubeMassFive := by
  constructor
  · exact weakCubeMassFive_rigid T
  · rintro ⟨c, rfl⟩ v
    rw [map_smul, weakCubeMassFive_closed, smul_zero]

end TernaryPoly.PolynomialFormWeakSmooth
