module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtHolomorphic
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwA

@[expose] public section


/-!
# The Eichler input of a weight vector from the weight gap

`EvenLevelThree.l3_holomorphicWt` shows that a smooth vector of rotation weight `-(n + 3)`
is holomorphic, using the Casimir weight gap of a *cohomological* representation.  While the
`Cohomological` witness is being constructed that gap is not available; here it is replaced by
`WeightGap σ n`: the raising image of such a vector has rotation weight `-(n + 1)`, hence vanishes.
`L3InputWt.ofGap` is the Eichler input built from a level-three weight vector with these data.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Automorphic.Constituent

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.MultiplicityOne (LevelThreeCusp levelThreeValues)
open TernaryPeriodPolynomials.EvenLevelThree

/-- **The raising image of a weight `-(n + 3)` smooth vector vanishes**, given the weight gap. -/
theorem l3_raising_eq_zero_of_gap {σ : CuspidalRepresentation} {n : ℕ} (gap : WeightGap σ n)
    (wt : ℤ) (hw : wt = -((n : ℤ) + 3)) (w : σ.smooth)
    (rotation : ∀ a : Circle, σ.π (atInfinity (binaryRotations a)) w.val =
      (a : ℂ) ^ wt • w.val) :
    cuspRaisingVector σ wt w.val = 0 := by
  have regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector σ w.val)
      UpperHalfPlane.upperHalfPlaneSet := cuspSmooth_le_affineSmooth σ w.property
  have rotated := cuspRaisingVector_rotation σ w.val wt regular rotation
  refine gap (wt + 2) _ rotated ?_
  have e : wt + 2 = -((n : ℤ) + 1) := by omega
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  omega

/-- **Every smooth vector of weight `-(n + 3)` is holomorphic**, given the weight gap. -/
theorem l3_holomorphic_of_gap {σ : CuspidalRepresentation} {n : ℕ} (gap : WeightGap σ n)
    (wt : ℤ) (hw : wt = -((n : ℤ) + 3)) (w : σ.smooth)
    (rotation : ∀ a : Circle, σ.π (atInfinity (binaryRotations a)) w.val =
      (a : ℂ) ^ wt • w.val) :
    DifferentiableOn ℂ (cuspWeightedAffineOrbitWt σ wt w.val)
      UpperHalfPlane.upperHalfPlaneSet := by
  have regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector σ w.val)
      UpperHalfPlane.upperHalfPlaneSet := cuspSmooth_le_affineSmooth σ w.property
  exact cuspWeightedAffineOrbit_holomorphicWt σ wt w.val (regular.differentiableOn (by simp))
    (l3_raising_eq_zero_of_gap gap wt hw w rotation)

/-- **The Eichler input of a level-three weight vector**, from the weight gap. -/
def L3InputWt.ofGap {σ : CuspidalRepresentation} {n : ℕ} (gap : WeightGap σ n)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (hσ : LevelThreeCusp σ) (wt : ℤ) (hw : wt = -((n : ℤ) + 3)) (w : σ.smooth)
    (level : w.val ∈ levelThreeValues σ)
    (rotation : ∀ a : Circle, σ.π (atInfinity (binaryRotations a)) w.val =
      (a : ℂ) ^ wt • w.val) : L3InputWt σ n where
  central_positive := central_positive
  cusp3 := hσ
  wt := wt
  weight := hw
  vector := w
  vector_level := level
  rotation := rotation
  holomorphic := l3_holomorphic_of_gap gap wt hw w rotation

end TernaryPeriodPolynomials.Automorphic.Constituent
