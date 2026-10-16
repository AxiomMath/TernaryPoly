module

public import TernaryPeriodPolynomials.SymmetricSpace.Siegel.ReductionRows
public import Mathlib.Algebra.Order.Round

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceSiegelReduction
open Matrix SymmetricSpacePositive SymmetricSpaceArithmeticProper

def pairing (S : Space) (v w : Vector) : ℝ := v ⬝ᵥ (S.val*ᵥw)

theorem pairing_symm (S : Space) (v w : Vector) : pairing S v w=pairing S w v := by
  have hs := Matrix.isHermitian_iff_isSymm.mp S.property.1.isHermitian
  change v ⬝ᵥ (S.val*ᵥw)=w ⬝ᵥ (S.val*ᵥv)
  simpa only [hs.eq] using Matrix.dotProduct_transpose_mulVec S.val v w

theorem pairing_add_smul (S : Space) (u v w : Vector) (r : ℝ) :
    pairing S u (v+r • w)=pairing S u v+r*pairing S u w := by
  simp [pairing,Matrix.mulVec_add,Matrix.mulVec_smul,dotProduct_add,dotProduct_smul]

theorem pairing_add_smul_left (S : Space) (v w u : Vector) (r : ℝ) :
    pairing S (v+r • w) u=pairing S v u+r*pairing S w u := by
  rw [pairing_symm S _ u,pairing_add_smul,pairing_symm S u v,pairing_symm S u w]

theorem energy_add_smul (S : Space) (v w : IntVector) (n : ℤ) :
    energy S (w+n • v)=energy S w+2*(n : ℝ)*pairing S (realVector v) (realVector w)+
      (n : ℝ)^2*energy S v := by
  rw [energy,realVector_add_smul]
  change pairing S (realVector w+(n : ℝ) • realVector v)
    (realVector w+(n : ℝ) • realVector v)=_
  simp only [pairing_add_smul_left,pairing_add_smul]
  rw [pairing_symm S (realVector w) (realVector v)]
  change energy S w+(n : ℝ)*pairing S (realVector v) (realVector w)+
    (n : ℝ)*(pairing S (realVector v) (realVector w)+(n : ℝ)*energy S v)=_
  ring

/-- Coefficient in the orthogonal projection onto the fixed last row. -/
def projectionCoefficient (S : Space) (v w : IntVector) : ℝ :=
  pairing S (realVector v) (realVector w)/energy S v

/-- Squared projected length, with no quotient-lattice abstraction assumed. -/
def projectedEnergy (S : Space) (v w : IntVector) : ℝ :=
  energy S w-(projectionCoefficient S v w)^2*energy S v

theorem projectionCoefficient_add_smul (S : Space) (v w : IntVector) (n : ℤ)
    (hv : energy S v≠0) :
    projectionCoefficient S v (w+n • v)=projectionCoefficient S v w+(n : ℝ) := by
  simp only [projectionCoefficient,realVector_add_smul,pairing_add_smul]
  change (_+(n : ℝ)*energy S v)/energy S v=_
  field_simp

theorem energy_recompose (S : Space) (v w : IntVector) :
    energy S w=projectedEnergy S v w+(projectionCoefficient S v w)^2*energy S v := by
  unfold projectedEnergy
  ring

theorem projectedEnergy_add_smul (S : Space) (v w : IntVector) (n : ℤ)
    (hv : energy S v≠0) : projectedEnergy S v (w+n • v)=projectedEnergy S v w := by
  rw [projectedEnergy,projectionCoefficient_add_smul S v w n hv,energy_add_smul,
    projectedEnergy,projectionCoefficient]
  field_simp
  ring

/-- Reducing along the last row gives an actual integral vector with bounded full energy. -/
theorem exists_reduced_projection (S : Space) (v w : IntVector) (hv : 0<energy S v) :
    ∃ n : ℤ, |projectionCoefficient S v (w+n • v)|≤1/2 ∧
      energy S (w+n • v)≤projectedEnergy S v w+energy S v/4 := by
  refine ⟨-round (projectionCoefficient S v w),?_,?_⟩
  · rw [projectionCoefficient_add_smul S v w _ (ne_of_gt hv)]
    simpa only [Int.cast_neg,sub_eq_add_neg] using abs_sub_round (projectionCoefficient S v w)
  · rw [energy_recompose S v _,projectedEnergy_add_smul S v w _ (ne_of_gt hv),
      projectionCoefficient_add_smul S v w _ (ne_of_gt hv)]
    have h := abs_sub_round (projectionCoefficient S v w)
    have hh := abs_le.mp h
    simp only [Int.cast_neg]
    have hs : (projectionCoefficient S v w-(round (projectionCoefficient S v w) : ℝ))^2≤1/4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (sub_nonneg.mpr hh.1)]
    have hm := mul_le_mul_of_nonneg_right hs hv.le
    nlinarith

end TernaryPoly.SymmetricSpaceSiegelReduction
