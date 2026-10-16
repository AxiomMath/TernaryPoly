module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.RadicalCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Section

@[expose] public section


/-!
# Scalar bookkeeping for the line source cocycle

The real line parabolic acts on binary forms through `lineStar`, whose scalar `θ(p) = χ(p) d_p⁻² det A_p`
contains the *signed* determinant of the Levi block.  Against the unsigned modulus `|det A|^{(n+3)/2}`
of the Levi cocycle this leaves the sign `sgn(det A)`, which is absorbed by the sign-twisted law of
the Levi cocycle.  This file collects the sign, the norm identities, the inverse `lineStar`
scalar and the orthogonality facts for blocks of the line parabolic.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm (finiteAdeleUnit)

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## The sign of the determinant -/

/-- The sign of the determinant of a real `GL₂` element, as a complex number. -/
def lineSgn (g : BinaryRealGL) : ℂ := if 0 < (GeneralLinearGroup.det g).val then 1 else -1

/-- The sign of `x` divided by `x` is the inverse of `|x|`. -/
theorem lsSgn_mul_inv_abs (x : ℝ) (hx : x ≠ 0) :
    (if 0 < x then (1 : ℂ) else -1) * ((x : ℝ) : ℂ)⁻¹ = ((|x| : ℝ) : ℂ)⁻¹ := by
  by_cases h : 0 < x
  · rw [ite_eq_left h, abs_of_pos h, one_mul]
  · have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp h) hx
    rw [ite_eq_right h, abs_of_neg hneg, Complex.ofReal_neg, inv_neg, neg_one_mul]

/-! ## Norm identities -/

theorem lsNormPower_det_succ (A : BinaryRealGL) (z : ℂ) :
    normPower (GeneralLinearGroup.det (atInfinity A)) (z + 1) =
      normPower (GeneralLinearGroup.det (atInfinity A)) z *
        ((|(GeneralLinearGroup.det A).val| : ℝ) : ℂ) := by
  have hpos : 0 < |(GeneralLinearGroup.det A).val| :=
    abs_pos.mpr (GeneralLinearGroup.det A).ne_zero
  rw [normPower_det_atInfinity, normPower_det_atInfinity,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_realAdeleUnit,
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_realAdeleUnit,
    add_mul, one_mul, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos]

theorem lsNormPower_real_two (s : ℝˣ) :
    normPower (realAdeleUnit s) 2 = ((s.val : ℝ) : ℂ) ^ 2 := by
  have hpos : 0 < |s.val| := abs_pos.mpr s.ne_zero
  have h2 : (2 : ℂ) * ((Real.log |s.val| : ℝ) : ℂ) =
      ((Real.log |s.val| : ℝ) : ℂ) + ((Real.log |s.val| : ℝ) : ℂ) := by ring
  rw [TernaryPeriodPolynomials.EisensteinRegularization.Helpers.normPower_realAdeleUnit,
    h2, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos, ← Complex.ofReal_mul,
    abs_mul_abs_self, Complex.ofReal_mul, sq]

theorem lsScalar_aux (c e M s D L : ℂ) (key : s * D⁻¹ = L⁻¹) (hL : L ≠ 0) :
    c * (s * (M * L)) * (e * D⁻¹) = c * (e * M) := by
  have hinv : L * L⁻¹ = 1 := mul_inv_cancel₀ hL
  linear_combination (c * e * M * L) * key + (c * e * M) * hinv

/-! ## The determinant of the Levi block -/

theorem lsDet_val (p : lineParabolic ℝ) : (lineLeviBlock p).val.det = lrDet p :=
  (Matrix.det_fin_two _).trans rfl

theorem lsDet (p : lineParabolic ℝ) :
    (GeneralLinearGroup.det (lineLeviBlock p)).val = lrDet p := by
  rw [GeneralLinearGroup.val_det_apply]
  exact lsDet_val p

theorem lsDetC (p : lineParabolic ℝ) :
    ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock p)) :
        ℂˣ) : ℂ) = ((lrDet p : ℝ) : ℂ) := by
  rw [GeneralLinearGroup.val_det_apply, ← lsDet_val p]
  exact (RingHom.map_det (algebraMap ℝ ℂ) (lineLeviBlock p).val).symm

theorem lsSgn_block (p : lineParabolic ℝ) :
    lineSgn (lineLeviBlock p) = if 0 < lrDet p then (1 : ℂ) else -1 := by
  unfold lineSgn
  rw [lsDet]

/-! ## The inverse scalar of `lineStar` -/

theorem lsTheta_inv (χ : RankOneCharacter) (hc : ∀ g : RealGL3, componentCharacter χ g = 1)
    (p : lineParabolic ℝ) :
    lineTheta χ p⁻¹ = ((p.1.val 0 0 : ℝ) : ℂ) ^ 2 * ((lrDet p : ℝ) : ℂ)⁻¹ := by
  have hA : algebraMap ℝ ℂ ((p.1.val 0 0)⁻¹) = ((p.1.val 0 0 : ℝ) : ℂ)⁻¹ :=
    map_inv₀ (algebraMap ℝ ℂ) _
  have hd : ((p.1.val 0 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lr_corner_ne_zero p.2)
  have hδ : ((lrDet p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lrDet_ne_zero p)
  rw [map_inv, lineTheta_apply, hc, lsDetC, hA]
  field_simp

/-- **The inverse Levi action on the block coefficient**: `lineStar` of the inverse composed with the
binary coefficient of the block is the scalar `d² / det A`. -/
theorem lsStar_inv_binaryCoefficient {n : ℕ} (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = 1) (p : lineParabolic ℝ)
    (v : Binary.HomogeneousPoly (n + 1)) :
    lineStar χ (n + 1) p⁻¹ (binaryCoefficient n (lineLeviBlock p) v) =
      (((p.1.val 0 0 : ℝ) : ℂ) ^ 2 * ((lrDet p : ℝ) : ℂ)⁻¹) • v := by
  have e : lineLeviBlock p⁻¹ = (lineLeviBlock p)⁻¹ := lineLeviBlockHom.map_inv p
  show lineTheta χ p⁻¹ •
      Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock p⁻¹))
        (Binary.homogeneousAction (n + 1) (-1)
          (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock p)) v) = _
  rw [lsTheta_inv χ hc p, e, _root_.map_inv, ← Module.End.mul_apply, ← map_mul,
    _root_.inv_mul_cancel, map_one, Module.End.one_apply]

/-- **The scalar of the radical law**: the sign of the twisted Levi cocycle cancels the sign of the
determinant in `d² / det A`, leaving `d² |det A|^β`. -/
theorem lsCore_scalar (c : ℂ) (p : lineParabolic ℝ) (β : ℂ) :
    c * (lineSgn (lineLeviBlock p) *
        normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p))) (β + 1)) *
      (((p.1.val 0 0 : ℝ) : ℂ) ^ 2 * ((lrDet p : ℝ) : ℂ)⁻¹) =
    c * (((p.1.val 0 0 : ℝ) : ℂ) ^ 2 *
      normPower (GeneralLinearGroup.det (atInfinity (lineLeviBlock p))) β) := by
  have hδ : lrDet p ≠ 0 := lrDet_ne_zero p
  have hl : ((|lrDet p| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hδ)
  have key := lsSgn_mul_inv_abs (lrDet p) hδ
  rw [lsNormPower_det_succ, lsDet, lsSgn_block]
  exact lsScalar_aux c _ _ _ _ _ key hl

/-! ## Orthogonal elements of the line parabolic -/

/-- The radical vanishes on the orthogonal elements of the line parabolic. -/
theorem lsRadical_orth {n : ℕ} (χ : RankOneCharacter) {m : lineParabolic ℝ}
    (ho : IsOrthogonalReal m.1) : lineRadical n χ m = 0 := by
  obtain ⟨h01, h02⟩ := orth_lineParabolic_block m.2 ho
  exact lineRadical_eq_zero_of_row_zero n χ m h01 h02

/-- The block of an orthogonal element of the line parabolic is orthogonal. -/
theorem lsLeviBlock_orth (m : lineParabolic ℝ) (hm : IsOrthogonalReal m.1) :
    (lineLeviBlock m).val.transpose * (lineLeviBlock m).val = 1 := by
  obtain ⟨h01, h02⟩ := orth_lineParabolic_block m.2 hm
  have hc : m.1.val.transpose * m.1.val = 1 := hm
  have c11 := congrFun (congrFun hc 1) 1
  have c12 := congrFun (congrFun hc 1) 2
  have c21 := congrFun (congrFun hc 2) 1
  have c22 := congrFun (congrFun hc 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h02] at c11 c12 c21 c22
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineLeviBlock, lrBlockP, lrLowerBlock, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-! ## Blocks of the generators -/

theorem lsCorner_levi (d : ℝˣ) (A : BinaryRealGL) :
    (((⟨lineLevi d A, lineLevi_mem d A⟩ : lineParabolic ℝ) : RealGL3).val 0 0 : ℝ) = (d : ℝ) :=
  lr_corner_levi d A

theorem lsCorner_unipotent (s t : ℝ) :
    (((⟨lineUnipotent s t, lineUnipotent_mem s t⟩ : lineParabolic ℝ) : RealGL3).val 0 0 : ℝ) = 1 :=
  rfl

theorem lsLeviBlock_unipotent (s t : ℝ) :
    lineLeviBlock ⟨lineUnipotent s t, lineUnipotent_mem s t⟩ = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-! ## The torus scalar -/

theorem lsTorus_scalar (χ : RankOneCharacter)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1) (t : Adelesˣ) :
    (((realUnitPart t).val : ℝ) : ℂ) ^ 2 *
        (χ.toMonoidHom (finiteAdeleUnit (finiteUnitPart t)) *
          normPower (finiteAdeleUnit (finiteUnitPart t)) 2) =
      χ.toMonoidHom t * normPower t 2 := by
  rw [character_split χ t, character_real_eq_one χ hχ, one_mul, normPower_split t 2,
    lsNormPower_real_two]
  ring

end TernaryPeriodPolynomials.SourceConstruction

end
