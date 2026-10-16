module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.Circle
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FourierUniqueness

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.StageTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ArchimedeanAveraging MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationFourier

theorem orbit_continuous (data : CuspidalRepresentation) (vector : data.H) :
    Continuous (fun parameter : Parameter => data.π (atInfinity (rotation parameter)) vector) :=
  ((data.continuous vector).comp atInfinity_continuous).comp rotation_continuous

theorem orbit_integrable (data : CuspidalRepresentation) (vector : data.H) :
    Integrable (fun parameter : Parameter => data.π (atInfinity (rotation parameter)) vector)
      AddCircle.haarAddCircle :=
  (orbit_continuous data vector).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem weighted_orbit_integrable (data : CuspidalRepresentation) (vector : data.H) (index : ℤ) :
    Integrable (fun parameter : Parameter =>
      fourier (-index) parameter • data.π (atInfinity (rotation parameter)) vector) AddCircle.haarAddCircle :=
  ((fourier (-index)).continuous.smul (orbit_continuous data vector)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The actual normalized Haar Fourier coefficient of the unitary rotation orbit. -/
noncomputable def modeVector (data : CuspidalRepresentation) (index : ℤ) (vector : data.H) : data.H :=
  fourierCoeff (fun parameter : Parameter => data.π (atInfinity (rotation parameter)) vector) index

theorem modeVector_norm_le (data : CuspidalRepresentation) (index : ℤ) (vector : data.H) :
    ‖modeVector data index vector‖ ≤ ‖vector‖ := by
  have estimate := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
    (Filter.Eventually.of_forall (fun parameter : Parameter => show
      ‖fourier (-index) parameter • data.π (atInfinity (rotation parameter)) vector‖ ≤ ‖vector‖ by
        rw [norm_smul, fourier_norm_one, data.unitary, one_mul]))
  simpa [modeVector, fourierCoeff] using estimate

theorem modeVector_add (data : CuspidalRepresentation) (index : ℤ) (first second : data.H) :
    modeVector data index (first + second) = modeVector data index first + modeVector data index second := by
  unfold modeVector
  have equality : (fun parameter : Parameter => data.π (atInfinity (rotation parameter)) (first + second)) =
      (fun parameter : Parameter => data.π (atInfinity (rotation parameter)) first) +
        (fun parameter : Parameter => data.π (atInfinity (rotation parameter)) second) := by
    funext parameter
    exact map_add _ _ _
  rw [equality]
  exact congrFun (fourierCoeff.add (orbit_integrable data first) (orbit_integrable data second)) index

theorem modeVector_smul (data : CuspidalRepresentation) (index : ℤ) (scalar : ℂ) (vector : data.H) :
    modeVector data index (scalar • vector) = scalar • modeVector data index vector := by
  unfold modeVector
  have equality : (fun parameter : Parameter => data.π (atInfinity (rotation parameter)) (scalar • vector)) =
      scalar • (fun parameter : Parameter => data.π (atInfinity (rotation parameter)) vector) := by
    funext parameter
    exact map_smul _ _ _
  rw [equality, fourierCoeff.const_smul]

noncomputable def modeOperator (data : CuspidalRepresentation) (index : ℤ) : data.H →L[ℂ] data.H :=
  let linear : data.H →ₗ[ℂ] data.H :=
    { toFun := modeVector data index
      map_add' := modeVector_add data index
      map_smul' := modeVector_smul data index }
  linear.mkContinuous 1 (fun vector => by
    change ‖modeVector data index vector‖ ≤ 1 * ‖vector‖
    simpa only [one_mul] using modeVector_norm_le data index vector)

theorem modeOperator_apply (data : CuspidalRepresentation) (index : ℤ) (vector : data.H) :
    modeOperator data index vector = modeVector data index vector := rfl

theorem modeOperator_norm_le (data : CuspidalRepresentation) (index : ℤ) :
    ‖modeOperator data index‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro vector
  change ‖modeVector data index vector‖ ≤ 1 * ‖vector‖
  simpa only [one_mul] using modeVector_norm_le data index vector

theorem modeVector_preserves_fixedSmooth (data : CuspidalRepresentation) (index : ℤ)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactLevel : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (fixed : vector.val ∈ fixedSubspace data level) :
    modeVector data index vector.val ∈ data.smooth ∧
      modeVector data index vector.val ∈ fixedSubspace data level := by
  exact integrable_weighted_parameter_integral_mem data level openness compactLevel vector fixed
    rotation rotation_continuous AddCircle.haarAddCircle (fourier (-index))
    ((fourier (-index)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem modeVector_mem_smooth (data : CuspidalRepresentation) (index : ℤ) (vector : data.smooth) :
    modeVector data index vector.val ∈ data.smooth := by
  obtain ⟨level, openness, compactLevel, fixed⟩ := ((data.smooth_exact vector.val).mp vector.property).2
  exact (modeVector_preserves_fixedSmooth data index level openness compactLevel vector fixed).1

theorem modeVector_eigen (data : CuspidalRepresentation) (index : ℤ) (vector : data.H) (parameter : Parameter) :
    data.π (atInfinity (rotation parameter)) (modeVector data index vector) =
      fourier index parameter • modeVector data index vector := by
  have integralMap := (unitaryOperator data (atInfinity (rotation parameter))).integral_comp_comm
    (weighted_orbit_integrable data vector index)
  change (∫ point : Parameter, data.π (atInfinity (rotation parameter))
      (fourier (-index) point • data.π (atInfinity (rotation point)) vector) ∂AddCircle.haarAddCircle) =
    data.π (atInfinity (rotation parameter)) (modeVector data index vector) at integralMap
  rw [← integralMap]
  calc
    _ = ∫ point : Parameter, fourier index parameter • (fourier (-index) (parameter + point) •
        data.π (atInfinity (rotation (parameter + point))) vector) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun point => by
        change data.π (atInfinity (rotation parameter))
            (fourier (-index) point • data.π (atInfinity (rotation point)) vector) =
          fourier index parameter • (fourier (-index) (parameter + point) •
            data.π (atInfinity (rotation (parameter + point))) vector)
        rw [map_smul, rotation_add, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, map_mul, Module.End.mul_apply,
          smul_smul, fourier_add_argument, ← mul_assoc, fourier_mul_neg, one_mul])
    _ = fourier index parameter • (∫ point : Parameter, fourier (-index) (parameter + point) •
        data.π (atInfinity (rotation (parameter + point))) vector ∂AddCircle.haarAddCircle) := integral_smul _ _
    _ = _ := congrArg (fun value : data.H => fourier index parameter • value)
      (integral_add_left_eq_self (fun point : Parameter => fourier (-index) point •
        data.π (atInfinity (rotation point)) vector) parameter)

theorem modeVector_eq_self_of_eigen (data : CuspidalRepresentation) (index : ℤ) (vector : data.H)
    (eigen : ∀ parameter : Parameter, data.π (atInfinity (rotation parameter)) vector =
      fourier index parameter • vector) : modeVector data index vector = vector := by
  unfold modeVector fourierCoeff
  simp only [eigen, smul_smul, mul_comm (fourier (-index) _) (fourier index _), fourier_mul_neg, one_smul]
  simp

theorem modeVector_idempotent (data : CuspidalRepresentation) (index : ℤ) (vector : data.H) :
    modeVector data index (modeVector data index vector) = modeVector data index vector :=
  modeVector_eq_self_of_eigen data index _ (modeVector_eigen data index vector)

theorem eq_zero_of_modes (data : CuspidalRepresentation) (vector : data.H)
    (coefficients : ∀ index : ℤ, modeVector data index vector = 0) : vector = 0 := by
  have orbitZero := FourierUniqueness.eq_zero _ (orbit_continuous data vector) coefficients
  have valueAtZero := congrFun orbitZero 0
  simpa only [rotation_zero, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one, map_one, Module.End.one_apply, Pi.zero_apply]
    using valueAtZero

theorem eq_of_modes (data : CuspidalRepresentation) (first second : data.H)
    (coefficients : ∀ index : ℤ, modeVector data index first = modeVector data index second) : first = second := by
  apply sub_eq_zero.mp
  apply eq_zero_of_modes data
  intro index
  change modeOperator data index (first - second) = 0
  rw [map_sub, modeOperator_apply, modeOperator_apply, coefficients, sub_self]

theorem modeVector_of_eigen (data : CuspidalRepresentation) (frequency index : ℤ) (vector : data.H)
    (eigen : ∀ parameter : Parameter, data.π (atInfinity (rotation parameter)) vector =
      fourier frequency parameter • vector) :
    modeVector data index vector = (Pi.single (M := fun _ : ℤ => data.H) frequency vector) index := by
  classical
  unfold modeVector
  have equality : (fun parameter : Parameter => data.π (atInfinity (rotation parameter)) vector) =
      (fun parameter : Parameter => fourier frequency parameter • vector) := funext eigen
  rw [equality, FourierUniqueness.fourierCoeff_smul_vector _ (fourier frequency).continuous,
    fourierCoeff_fourier]
  by_cases same : index = frequency
  · subst index
    simp
  · simp [same]

theorem modeVector_comp (data : CuspidalRepresentation) (frequency index : ℤ) (vector : data.H) :
    modeVector data index (modeVector data frequency vector) =
      (Pi.single (M := fun _ : ℤ => data.H) frequency (modeVector data frequency vector)) index :=
  modeVector_of_eigen data frequency index _ (modeVector_eigen data frequency vector)

noncomputable def smoothMode (data : CuspidalRepresentation) (index : ℤ) : data.smooth →ₗ[ℂ] data.smooth where
  toFun vector := ⟨modeVector data index vector.val, modeVector_mem_smooth data index vector⟩
  map_add' first second := Subtype.ext (modeVector_add data index first.val second.val)
  map_smul' scalar vector := Subtype.ext (modeVector_smul data index scalar vector.val)

theorem smoothMode_realize_eigen (data : CuspidalRepresentation) (index : ℤ) (vector : data.smooth)
    (point : BinaryAdelicGL) (parameter : Parameter) :
    data.realize (smoothMode data index vector) (point * atInfinity (rotation parameter)) =
      fourier index parameter * data.realize (smoothMode data index vector) point := by
  have equality :
      (⟨data.π (atInfinity (rotation parameter)) (smoothMode data index vector).val,
        data.smooth_stable _ _ (smoothMode data index vector).property⟩ : data.smooth) =
      fourier index parameter • smoothMode data index vector :=
    Subtype.ext (modeVector_eigen data index vector.val parameter)
  rw [← data.equivariant, equality, map_smul]
  rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationFourier
