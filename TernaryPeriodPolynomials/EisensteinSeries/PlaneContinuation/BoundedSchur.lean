module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CuspidalHilbert
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Analysis.Analytic.RadiusLiminf
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BoundedSchur

noncomputable instance operatorCStarAlgebra (data : CuspidalRepresentation) :
    CStarAlgebra (data.H →L[ℂ] data.H) := .mk

theorem injective_of_commuting (data : CuspidalRepresentation) (operator : data.H →L[ℂ] data.H)
    (commuting : ∀ matrix, Commute operator (unitaryOperator data matrix)) (nonzero : operator ≠ 0) :
    Function.Injective operator := by
  have stable (matrix : BinaryAdelicGL) (vector : data.H) (membership : vector ∈ operator.ker) :
      data.π matrix vector ∈ operator.ker := by
    change operator (unitaryOperator data matrix vector) = 0
    have equality := congrArg (fun value : data.H →L[ℂ] data.H => value vector) (commuting matrix).eq
    change operator (unitaryOperator data matrix vector) = unitaryOperator data matrix (operator vector) at equality
    rw [equality, show operator vector = 0 from membership, map_zero]
  rcases data.irreducible operator.ker operator.isClosed_ker stable with zeroKernel | fullKernel
  · exact LinearMap.ker_eq_bot.mp zeroKernel
  · apply False.elim
    apply nonzero
    ext vector
    have membership : vector ∈ operator.ker := by rw [fullKernel]; trivial
    exact membership

theorem product_ne_zero (data : CuspidalRepresentation) (first second : data.H →L[ℂ] data.H)
    (commuting : ∀ matrix, Commute first (unitaryOperator data matrix))
    (firstNonzero : first ≠ 0) (secondNonzero : second ≠ 0) : first * second ≠ 0 := by
  intro vanishing
  apply secondNonzero
  ext vector
  apply injective_of_commuting data first commuting firstNonzero
  have equality := congrArg (fun value : data.H →L[ℂ] data.H => value vector) vanishing
  simpa only [mul_apply_eq_comp, zero_apply, map_zero] using equality

theorem spectrum_no_lt (data : CuspidalRepresentation) (operator : data.H →L[ℂ] data.H)
    (selfAdjoint : IsSelfAdjoint operator)
    (commuting : ∀ matrix, Commute operator (unitaryOperator data matrix))
    (left right : ℝ) (leftMember : left ∈ spectrum ℝ operator) (rightMember : right ∈ spectrum ℝ operator) :
    ¬ left < right := by
  intro strict
  let midpoint := (left + right) / 2
  let positive : ℝ → ℝ := fun value => max (value - midpoint) 0
  let negative : ℝ → ℝ := fun value => max (midpoint - value) 0
  have positiveContinuous : Continuous positive := (continuous_id.sub continuous_const).max continuous_const
  have negativeContinuous : Continuous negative := (continuous_const.sub continuous_id).max continuous_const
  have positiveNonzero : cfc positive operator ≠ 0 := by
    intro vanishing
    have equality := (cfc_eq_cfc_iff_eqOn selfAdjoint positiveContinuous.continuousOn
      continuous_const.continuousOn).mp (show cfc positive operator = cfc (fun _ : ℝ => 0) operator by
        rw [cfc_const 0 operator selfAdjoint, map_zero]; exact vanishing)
    have pointEquality := equality rightMember
    dsimp [positive, midpoint] at pointEquality
    rw [max_eq_left (by linarith)] at pointEquality
    linarith
  have negativeNonzero : cfc negative operator ≠ 0 := by
    intro vanishing
    have equality := (cfc_eq_cfc_iff_eqOn selfAdjoint negativeContinuous.continuousOn
      continuous_const.continuousOn).mp (show cfc negative operator = cfc (fun _ : ℝ => 0) operator by
        rw [cfc_const 0 operator selfAdjoint, map_zero]; exact vanishing)
    have pointEquality := equality leftMember
    dsimp [negative, midpoint] at pointEquality
    rw [max_eq_left (by linarith)] at pointEquality
    linarith
  have productZero : cfc positive operator * cfc negative operator = 0 := by
    rw [← cfc_mul positive negative operator positiveContinuous.continuousOn negativeContinuous.continuousOn]
    have zeroFunction : (fun value => positive value * negative value) = fun _ => (0 : ℝ) := by
      funext value
      dsimp [positive, negative]
      rcases le_total value midpoint with bound | bound
      · rw [max_eq_right (sub_nonpos.mpr bound), zero_mul]
      · rw [max_eq_right (sub_nonpos.mpr bound), mul_zero]
    rw [zeroFunction, cfc_const 0 operator selfAdjoint, map_zero]
  exact product_ne_zero data _ _ (fun matrix => (commuting matrix).cfc_real positive)
    positiveNonzero negativeNonzero productZero

theorem selfAdjoint_scalar (data : CuspidalRepresentation) (operator : data.H →L[ℂ] data.H)
    (selfAdjoint : IsSelfAdjoint operator)
    (commuting : ∀ matrix, Commute operator (unitaryOperator data matrix)) :
    ∃ value : ℝ, operator = (value : ℂ) • ContinuousLinearMap.id ℂ data.H := by
  let _ := data.nontrivial
  obtain ⟨value, membership⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) operator selfAdjoint
  have constantSpectrum : Set.EqOn (fun point : ℝ => point) (fun _ => value) (spectrum ℝ operator) := by
    intro point pointMember
    exact le_antisymm
      (le_of_not_gt (spectrum_no_lt data operator selfAdjoint commuting value point membership pointMember))
      (le_of_not_gt (spectrum_no_lt data operator selfAdjoint commuting point value pointMember membership))
  have equality := (cfc_eq_cfc_iff_eqOn selfAdjoint continuous_id.continuousOn
    continuous_const.continuousOn).mpr constantSpectrum
  rw [cfc_id ℝ operator selfAdjoint, cfc_const value operator selfAdjoint] at equality
  exact ⟨value, equality⟩

theorem unitary_mul (data : CuspidalRepresentation) (first second : BinaryAdelicGL) :
    unitaryOperator data (first * second) = unitaryOperator data first * unitaryOperator data second := by
  ext vector
  exact congrArg (fun value : Module.End ℂ data.H => value vector) (map_mul data.π first second)

theorem unitary_one (data : CuspidalRepresentation) : unitaryOperator data 1 = 1 := by
  ext vector
  exact congrArg (fun value : Module.End ℂ data.H => value vector) (map_one data.π)

theorem unitary_inner (data : CuspidalRepresentation) (matrix : BinaryAdelicGL) (first second : data.H) :
    inner ℂ (unitaryOperator data matrix first) (unitaryOperator data matrix second) = inner ℂ first second := by
  let isometry : data.H →ₗᵢ[ℂ] data.H := ⟨data.π matrix, data.unitary matrix⟩
  exact isometry.inner_map_map first second

theorem unitary_star (data : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    star (unitaryOperator data matrix) = unitaryOperator data matrix⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro first second
  have equality := unitary_inner data matrix (unitaryOperator data matrix⁻¹ first) second
  have cancel : unitaryOperator data matrix (unitaryOperator data matrix⁻¹ first) = first := by
    change (unitaryOperator data matrix * unitaryOperator data matrix⁻¹) first = first
    rw [← unitary_mul, mul_inv_cancel, unitary_one]
    rfl
  rw [cancel] at equality
  exact equality.symm

theorem star_commuting (data : CuspidalRepresentation) (operator : data.H →L[ℂ] data.H)
    (commuting : ∀ matrix, Commute operator (unitaryOperator data matrix)) :
    ∀ matrix, Commute (star operator) (unitaryOperator data matrix) := by
  intro matrix
  have equality := (commuting matrix⁻¹).star_star
  rw [unitary_star, inv_inv] at equality
  exact equality

/-- Hilbert-space Schur's lemma for the exact topological irreducibility hypothesis. -/
theorem scalar (data : CuspidalRepresentation) (operator : data.H →L[ℂ] data.H)
    (commuting : ∀ matrix, Commute operator (unitaryOperator data matrix)) :
    ∃ value : ℂ, operator = value • ContinuousLinearMap.id ℂ data.H := by
  have adjointCommuting := star_commuting data operator commuting
  have realCommuting : ∀ matrix, Commute (operator + star operator) (unitaryOperator data matrix) :=
    fun matrix => (commuting matrix).add_left (adjointCommuting matrix)
  have imaginaryCommuting : ∀ matrix,
      Commute (Complex.I • (operator - star operator)) (unitaryOperator data matrix) := by
    intro matrix
    change (Complex.I • (operator - star operator)) * unitaryOperator data matrix =
      unitaryOperator data matrix * (Complex.I • (operator - star operator))
    simp only [smul_mul_assoc, mul_smul_comm]
    rw [((commuting matrix).sub_left (adjointCommuting matrix)).eq]
  have imaginarySelfAdjoint : IsSelfAdjoint (Complex.I • (operator - star operator)) := by
    rw [isSelfAdjoint_iff]
    simp only [star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I]
    module
  obtain ⟨realValue, realEquality⟩ := selfAdjoint_scalar data _ (IsSelfAdjoint.add_star_self operator) realCommuting
  obtain ⟨imaginaryValue, imaginaryEquality⟩ := selfAdjoint_scalar data _ imaginarySelfAdjoint imaginaryCommuting
  refine ⟨((realValue : ℂ) - Complex.I * imaginaryValue) / 2, ?_⟩
  have reconstruction : (2 : ℂ) • operator =
      (operator + star operator) - Complex.I • (Complex.I • (operator - star operator)) := by
    rw [smul_smul, Complex.I_mul_I]
    module
  rw [realEquality, imaginaryEquality] at reconstruction
  apply (smul_right_inj (M := data.H →L[ℂ] data.H) (r := (2 : ℂ)) (by norm_num)).mp
  rw [reconstruction]
  simp only [smul_smul]
  module

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BoundedSchur
