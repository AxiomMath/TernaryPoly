module

public import TernaryPeriodPolynomials.Polynomial.Operators
public import TernaryPeriodPolynomials.Polynomial.Homogeneous

@[expose] public section


open MvPolynomial

noncomputable section

namespace TernaryPoly

/-- Restriction to the first coordinate axis, with parameter `X 0`. -/
def axisX : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial := bind₁ ![X 0, 0, 0]

/-- Restriction to the second coordinate axis, with parameter `X 0`. -/
def axisY : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial := bind₁ ![0, X 0, 0]

/-- Restriction to the third coordinate axis, with parameter `X 0`. -/
def axisZ : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial := bind₁ ![0, 0, X 0]

theorem axisZ_comp_A : axisZ.comp A = axisZ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [axisZ, A, AlgHom.comp_apply]

theorem axisZ_comp_A2 : axisZ.comp A2 = axisZ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [axisZ, A2, AlgHom.comp_apply]

theorem axisZ_comp_C : axisZ.comp C = axisY := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [axisZ, axisY, C, AlgHom.comp_apply]

theorem axisY_comp_C : axisY.comp C = axisX := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [axisY, axisX, C, AlgHom.comp_apply]

@[simp] theorem axisZ_A (f : TernaryPolynomial) : axisZ (A f) = axisZ f :=
  DFunLike.congr_fun axisZ_comp_A f

@[simp] theorem axisZ_A2 (f : TernaryPolynomial) : axisZ (A2 f) = axisZ f :=
  DFunLike.congr_fun axisZ_comp_A2 f

theorem axisZ_C (f : TernaryPolynomial) : axisZ (C f) = axisY f :=
  DFunLike.congr_fun axisZ_comp_C f

theorem axisY_C (f : TernaryPolynomial) : axisY (C f) = axisX f :=
  DFunLike.congr_fun axisY_comp_C f

/-- The norm relation alone kills the third coordinate axis. -/
theorem axisZ_eq_zero_of_norm {f : TernaryPolynomial} (hf : N f = 0) :
    axisZ f = 0 := by
  have h : axisZ f + axisZ f + axisZ f = 0 := by
    simpa only [N_apply, map_add, axisZ_A, axisZ_A2, map_zero] using
      congrArg axisZ hf
  have h3 : (3 : ℚ) • axisZ f = 0 := by
    simpa only [show (3 : ℚ) = 1 + 1 + 1 by norm_num, add_smul, one_smul] using h
  exact (smul_eq_zero.mp h3).resolve_left (by norm_num)

theorem PeriodRelations.axisZ_eq_zero {f : TernaryPolynomial} (hf : PeriodRelations f) :
    axisZ f = 0 := axisZ_eq_zero_of_norm hf.2

theorem PeriodRelations.axisY_eq_zero {f : TernaryPolynomial} (hf : PeriodRelations f) :
    axisY f = 0 := by
  rw [← axisZ_C, hf.1, hf.axisZ_eq_zero]

theorem PeriodRelations.axisX_eq_zero {f : TernaryPolynomial} (hf : PeriodRelations f) :
    axisX f = 0 := by
  rw [← axisY_C, hf.1, hf.axisY_eq_zero]

/-- Every period polynomial vanishes on all three coordinate axes. -/
theorem PeriodRelations.axis_restrictions_eq_zero {f : TernaryPolynomial}
    (hf : PeriodRelations f) :
    bind₁ ![X 0, 0, 0] f = (0 : TernaryPolynomial) ∧
      bind₁ ![0, X 0, 0] f = (0 : TernaryPolynomial) ∧
      bind₁ ![0, 0, X 0] f = (0 : TernaryPolynomial) :=
  ⟨hf.axisX_eq_zero, hf.axisY_eq_zero, hf.axisZ_eq_zero⟩

/-- A constant homogeneous solution of the period relations is zero. -/
theorem PeriodRelations.eq_zero_of_isHomogeneous_zero {f : TernaryPolynomial}
    (hf : PeriodRelations f) (hdeg : f.IsHomogeneous 0) : f = 0 := by
  have hc : MvPolynomial.C (f.coeff 0) = f := by
    rw [← homogeneousComponent_zero, homogeneousComponent_eq_self hdeg]
  have hz := hf.axisZ_eq_zero
  rw [← hc] at hz ⊢
  simpa [axisZ] using hz

/-- The degree-zero homogeneous component of a period polynomial vanishes. -/
theorem PeriodRelations.homogeneousComponent_zero_eq_zero {f : TernaryPolynomial}
    (hf : PeriodRelations f) : homogeneousComponent 0 f = 0 := by
  have hr : PeriodRelations (homogeneousComponent 0 f) :=
    homogeneousComponent_relations f hf.1 hf.2 0
  exact hr.eq_zero_of_isHomogeneous_zero (homogeneousComponent_isHomogeneous 0 f)

/-- In particular, every period polynomial has zero constant coefficient. -/
theorem PeriodRelations.coeff_zero_eq_zero {f : TernaryPolynomial}
    (hf : PeriodRelations f) : f.coeff 0 = 0 := by
  have h := hf.homogeneousComponent_zero_eq_zero
  rw [homogeneousComponent_zero] at h
  simpa using congrArg constantCoeff h

end TernaryPoly
