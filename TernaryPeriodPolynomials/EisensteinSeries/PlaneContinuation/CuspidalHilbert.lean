module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.Level

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalHilbert

theorem binaryValues_zero (data : CuspidalRepresentation) (degree : ℕ) :
    BinaryValues data degree (fun _ => 0) := by
  intro monomial
  refine ⟨0, ?_⟩
  ext matrix
  simp

theorem binaryValues_eq_zero_of_smooth_eq_bot (data : CuspidalRepresentation) (degree : ℕ)
    (zeroSmooth : data.smooth = ⊥)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : BinaryValues data degree function) : function = 0 := by
  funext matrix
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  obtain ⟨vector, realization⟩ := values monomial
  have zeroVector : vector = 0 := by
    apply Subtype.ext
    exact (Submodule.mem_bot ℂ).mp ((le_of_eq zeroSmooth) vector.property)
  have coefficientEquality := congrFun realization matrix
  rw [zeroVector, map_zero, Pi.zero_apply] at coefficientEquality
  exact coefficientEquality.symm

theorem cohomological_smooth_ne_bot {degree : ℕ} {data : CuspidalRepresentation}
    (cohomology : Cohomological data degree) : data.smooth ≠ ⊥ := by
  intro zeroSmooth
  obtain ⟨cocycle, values, _, _, _, nontrivialClass⟩ := cohomology
  have zeroCocycle (matrix : BinaryRealGL) : cocycle matrix = 0 :=
    binaryValues_eq_zero_of_smooth_eq_bot data degree zeroSmooth _ (values matrix)
  apply nontrivialClass
  refine ⟨fun _ => 0, binaryValues_zero data degree, ?_⟩
  intro matrix point
  rw [zeroCocycle]
  simp [binaryCohomologicalAction]

theorem smooth_closure_stable (data : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    Set.MapsTo (data.π matrix) (data.smooth.topologicalClosure : Set data.H)
      (data.smooth.topologicalClosure : Set data.H) :=
  (show Set.MapsTo (data.π matrix) (data.smooth : Set data.H) (data.smooth : Set data.H)
    from data.smooth_stable matrix).closure (unitaryOperator data matrix).continuous

theorem smooth_closure_eq_top (data : CuspidalRepresentation) (nonzeroSmooth : data.smooth ≠ ⊥) :
    data.smooth.topologicalClosure = ⊤ := by
  rcases data.irreducible data.smooth.topologicalClosure data.smooth.isClosed_topologicalClosure
      (fun matrix _ membership => smooth_closure_stable data matrix membership) with zeroClosure | fullClosure
  · exact False.elim (nonzeroSmooth (eq_bot_iff.mpr
      (zeroClosure ▸ data.smooth.le_topologicalClosure)))
  · exact fullClosure

theorem smooth_dense {degree : ℕ} (data : InducingData degree) :
    Dense (data.cusp.smooth : Set data.cusp.H) := by
  apply dense_iff_closure_eq.mpr
  change (data.cusp.smooth.topologicalClosure : Set data.cusp.H) = Set.univ
  rw [smooth_closure_eq_top data.cusp (cohomological_smooth_ne_bot data.cohomological)]
  rfl

theorem exists_nonzero_smooth {degree : ℕ} (data : InducingData degree) :
    ∃ vector : data.cusp.smooth, vector.val ≠ 0 := by
  obtain ⟨vector, membership, nonzero⟩ :=
    (Submodule.ne_bot_iff data.cusp.smooth).mp (cohomological_smooth_ne_bot data.cohomological)
  exact ⟨⟨vector, membership⟩, nonzero⟩

theorem scalar_commute (scalar : Adelesˣ) (matrix : BinaryAdelicGL) :
    matrix * Matrix.GeneralLinearGroup.scalar (Fin 2) scalar =
      Matrix.GeneralLinearGroup.scalar (Fin 2) scalar * matrix :=
  (Matrix.GeneralLinearGroup.scalar_commute scalar matrix).symm

theorem smooth_central (data : CuspidalRepresentation) (scalar : Adelesˣ) (vector : data.smooth) :
    data.π (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar) vector.val =
      data.centralCharacter scalar • vector.val := by
  have vectorEquality :
      (⟨data.π (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar) vector.val,
        data.smooth_stable _ _ vector.property⟩ : data.smooth) = data.centralCharacter scalar • vector := by
    apply data.injective
    funext matrix
    rw [data.equivariant, scalar_commute, data.central, map_smul]
    rfl
  exact congrArg Subtype.val vectorEquality

theorem central {degree : ℕ} (data : InducingData degree) (scalar : Adelesˣ) (vector : data.cusp.H) :
    data.cusp.π (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar) vector =
      data.cusp.centralCharacter scalar • vector := by
  have equality : Set.EqOn
      (data.cusp.π (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar))
      (fun value => data.cusp.centralCharacter scalar • value)
      (data.cusp.smooth : Set data.cusp.H) := by
    intro value membership
    exact smooth_central data.cusp scalar ⟨value, membership⟩
  exact equality.closure
    (unitaryOperator data.cusp (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar)).continuous
    (continuous_const.smul continuous_id) (smooth_dense data vector)

theorem exists_nonzero_realization {degree : ℕ} (data : InducingData degree) :
    ∃ vector : data.cusp.smooth, ∃ matrix : BinaryAdelicGL, data.cusp.realize vector matrix ≠ 0 := by
  classical
  obtain ⟨vector, nonzero⟩ := exists_nonzero_smooth data
  refine ⟨vector, ?_⟩
  by_contra! zeroRealization
  have zeroVector : vector = 0 := data.cusp.injective (by
    ext matrix
    rw [zeroRealization, map_zero, Pi.zero_apply])
  exact nonzero (congrArg Subtype.val zeroVector)

theorem centralCharacter_rational {degree : ℕ} (data : InducingData degree) (scalar : ℚˣ) :
    data.cusp.centralCharacter (Units.map rationalAdele.toMonoidHom scalar) = 1 := by
  obtain ⟨vector, matrix, nonzero⟩ := exists_nonzero_realization data
  have equality := data.cusp.central (Units.map rationalAdele.toMonoidHom scalar) vector matrix
  have scalarMap : Matrix.GeneralLinearGroup.map rationalAdele
      (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map rationalAdele.toMonoidHom scalar) :=
    Matrix.GeneralLinearGroup.map_scalar rationalAdele scalar
  rw [← scalarMap, data.cusp.leftRational] at equality
  apply mul_right_cancel₀ nonzero
  simpa only [one_mul] using equality.symm

theorem scalar_continuous : Continuous (Matrix.GeneralLinearGroup.scalar (Fin 2) (R := Adeles)) := by
  apply Units.continuous_map
  exact (continuous_pi (fun _ : Fin 2 =>
    (continuous_id : Continuous (fun value : Adeles => value)))).matrix_diagonal

theorem centralCharacter_continuous {degree : ℕ} (data : InducingData degree) :
    Continuous data.cusp.centralCharacter := by
  obtain ⟨vector, nonzero⟩ := exists_nonzero_smooth data
  have innerNonzero : inner ℂ vector.val vector.val ≠ 0 := inner_self_ne_zero.mpr nonzero
  have formula : (fun scalar => data.cusp.centralCharacter scalar) =
      fun scalar => inner ℂ vector.val
        (data.cusp.π (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar) vector.val) /
          inner ℂ vector.val vector.val := by
    funext scalar
    rw [central, inner_smul_right, mul_div_cancel_right₀ _ innerNonzero]
  rw [show (data.cusp.centralCharacter : Adelesˣ → ℂ) = _ from formula]
  exact (continuous_const.inner ((data.cusp.continuous vector.val).comp scalar_continuous)).div_const _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalHilbert
