module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtOrbit

@[expose] public section


/-!
# Holomorphy of weight `-(n + 3)` vectors, for every parity of `n`

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins of `l3_raising_eq_zero` and `l3_holomorphic` with an integer rotation weight `wt = -(n + 3)`
in place of `2 * halfWeight`, so that even degrees `n` (odd weights) are covered.  The circular
orbit lemma `l3_circularOrbit_eq` is already weight-generic and is reused.
-/

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
  (binaryCircleRotation cuspCircularOrbit cuspRotationProjection_of_character
    cohomological_hilbert_projection_zero)
open TernaryPeriodPolynomials.SourceConstruction (l3_circularOrbit_eq)

/-- **The raising image of a weight `-(n + 3)` smooth vector vanishes.** -/
theorem l3_raising_eq_zeroWt {σ : CuspidalRepresentation} {n : ℕ} (coh : Cohomological σ n)
    (wt : ℤ) (hw : wt = -((n : ℤ) + 3)) (w : σ.smooth)
    (rotation : ∀ a : Circle, σ.π (atInfinity (binaryRotations a)) w.val =
      (a : ℂ) ^ wt • w.val) :
    cuspRaisingVector σ wt w.val = 0 := by
  have regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector σ w.val)
      UpperHalfPlane.upperHalfPlaneSet := cuspSmooth_le_affineSmooth σ w.property
  have rotated := cuspRaisingVector_rotation σ w.val wt regular rotation
  have character := l3_circularOrbit_eq σ (cuspRaisingVector σ wt w.val)
    (wt + 2) rotated
  have value : (((-(wt + 2) : ℤ)) : ℝ) = (n : ℝ) + 1 := by
    have e : (-(wt + 2) : ℤ) = (n : ℤ) + 1 := by omega
    exact_mod_cast e
  have forbidden : |(((-(wt + 2) : ℤ)) : ℝ)| < (n : ℝ) + 3 := by
    have nonneg : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [value, abs_of_nonneg nonneg]
    linarith
  have projection_zero := cohomological_hilbert_projection_zero coh (-(wt + 2))
    forbidden (cuspRaisingVector σ wt w.val)
  have projected := cuspRotationProjection_of_character σ (-(wt + 2))
    (-(wt + 2)) _ character
  rw [ite_eq_left rfl, projection_zero] at projected
  exact projected.symm

/-- **Every smooth vector of weight `-(n + 3)` is holomorphic** (no level hypothesis). -/
theorem l3_holomorphicWt {σ : CuspidalRepresentation} {n : ℕ} (coh : Cohomological σ n)
    (wt : ℤ) (hw : wt = -((n : ℤ) + 3)) (w : σ.smooth)
    (rotation : ∀ a : Circle, σ.π (atInfinity (binaryRotations a)) w.val =
      (a : ℂ) ^ wt • w.val) :
    DifferentiableOn ℂ (cuspWeightedAffineOrbitWt σ wt w.val)
      UpperHalfPlane.upperHalfPlaneSet := by
  have regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector σ w.val)
      UpperHalfPlane.upperHalfPlaneSet := cuspSmooth_le_affineSmooth σ w.property
  exact cuspWeightedAffineOrbit_holomorphicWt σ wt w.val (regular.differentiableOn (by simp))
    (l3_raising_eq_zeroWt coh wt hw w rotation)

end TernaryPeriodPolynomials.EvenLevelThree
