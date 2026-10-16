module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Bounds
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IntegerReduction
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.PSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds

noncomputable abbrev integralLattice : Submodule ℤ (EuclideanSpace ℝ (Fin 3)) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)

theorem integerVector_mem_lattice (vector : Fin 3 → ℤ) :
    (WithLp.toLp 2 (fun column => (vector column : ℝ)) : EuclideanSpace ℝ (Fin 3)) ∈
      integralLattice := by
  have expansion : (WithLp.toLp 2 (fun column => (vector column : ℝ)) :
      EuclideanSpace ℝ (Fin 3)) =
      ∑ column : Fin 3, vector column • (EuclideanSpace.basisFun (Fin 3) ℝ) column := by
    ext column
    simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
  rw [expansion]
  exact Submodule.sum_mem _ (fun column _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨column, rfl⟩))

noncomputable def integralFlagLatticeRow (flag : Flags .plane) : integralLattice :=
  ⟨WithLp.toLp 2 (fun column =>
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ)),
    integerVector_mem_lattice _⟩

theorem integralFlagLatticeRow_injective : Function.Injective integralFlagLatticeRow := by
  intro first second equality
  apply TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow_injective
  funext column
  have coordinateEquality := congrArg
    (fun vector : integralLattice => vector.val column) equality
  exact Int.cast_injective coordinateEquality

theorem norm_integralFlagLatticeRow (flag : Flags .plane) :
    ‖integralFlagLatticeRow flag‖ =
      ‖(WithLp.toLp 2 (fun column =>
        (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ)) :
          EuclideanSpace ℝ (Fin 3))‖ := rfl

theorem summable_integralFlagRow_rpow (exponent : ℝ) (exponentBound : exponent < -3) :
    Summable (fun flag : Flags .plane =>
      ‖(WithLp.toLp 2 (fun column =>
        (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ)) :
          EuclideanSpace ℝ (Fin 3))‖ ^ exponent) := by
  have rankEquality : Module.finrank ℤ integralLattice = 3 := by
    rw [ZLattice.rank ℝ integralLattice]
    simp
  have summableLattice := ZLattice.summable_norm_rpow integralLattice exponent
    (by simpa only [rankEquality, Nat.cast_ofNat] using exponentBound)
  have result : Summable (fun flag : Flags .plane =>
      ‖integralFlagLatticeRow flag‖ ^ exponent) :=
    summableLattice.comp_injective integralFlagLatticeRow_injective
  apply result.congr
  intro flag
  rw [norm_integralFlagLatticeRow]

theorem abs_det_integral_real (matrix : IntegralGL3) :
    |(Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) matrix).val.det| = 1 := by
  have determinantValue : (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) matrix).val.det =
      (matrix.val.det : ℝ) := (RingHom.map_det (Int.castRingHom ℝ) matrix.val).symm
  rw [determinantValue]
  have determinantUnit : IsUnit matrix.val.det :=
    (Matrix.GeneralLinearGroup.det matrix).isUnit
  exact_mod_cast Int.isUnit_iff_abs_eq.mp determinantUnit

theorem summable_cuspVectors_of_lattice_rows {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin 3)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    {index : Type*} (matrices : index → RealGL3) (rows : index → lattice)
    (rowsInjective : Function.Injective rows)
    (rowValues : ∀ i, (rows i).val =
      WithLp.toLp 2 (fun column : Fin 3 => (matrices i).val 2 column))
    (determinants : ∀ i, |(matrices i).val.det| = 1)
    (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Summable (fun i =>
      (planeCuspVector (flatSection.1 parameter) (atInfinity (matrices i))).val) := by
  have latticeRank : Module.finrank ℤ lattice = 3 := by
    rw [ZLattice.rank ℝ lattice]
    simp
  have exponentBound : -(parameter.re + ((degree : ℝ) + 6) / 2) <
      -(Module.finrank ℤ lattice : ℝ) := by
    rw [latticeRank]
    norm_num
    linarith
  have latticeSummable := ZLattice.summable_norm_rpow lattice
    (-(parameter.re + ((degree : ℝ) + 6) / 2)) exponentBound
  obtain ⟨bound, _, matrixBound⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Bounds.flatSection_real_cuspVector_rpow_bound flatSection
  apply ((latticeSummable.comp_injective rowsInjective).mul_right bound).of_norm_bounded
  intro i
  change ‖(planeCuspVector (flatSection.1 parameter) (atInfinity (matrices i))).val‖ ≤
    ‖(rows i).val‖ ^ (-(parameter.re + ((degree : ℝ) + 6) / 2)) * bound
  rw [rowValues]
  simpa only [determinants, Real.one_rpow, one_mul] using matrixBound parameter (matrices i)

theorem summable_real_flag_cuspVectors {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Summable (fun flag : Flags .plane =>
      (planeCuspVector (flatSection.1 parameter)
        (atInfinity (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ)
          (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)⁻¹))).val) := by
  exact summable_cuspVectors_of_lattice_rows flatSection integralLattice
    (fun flag => Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ)
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)⁻¹)
    integralFlagLatticeRow integralFlagLatticeRow_injective (fun _ => rfl)
    (fun _ => abs_det_integral_real _) parameter rightHalfPlane

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds
