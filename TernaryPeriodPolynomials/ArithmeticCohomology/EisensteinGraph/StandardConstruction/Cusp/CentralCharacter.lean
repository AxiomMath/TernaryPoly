module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BinaryCentralCharacter
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.Realization

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspCentralCharacter

theorem scalar_continuous :
    Continuous (GeneralLinearGroup.scalar (Fin 2) : Adelesˣ → BinaryAdelicGL) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun unit : Adelesˣ => Matrix.scalar (Fin 2) unit.val)
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    by_cases equality : row = column
    · simpa only [Matrix.scalar_apply, Matrix.diagonal_apply, equality, ite_true] using
        Units.continuous_val (M := Adeles)
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply, equality, ite_false]
      exact continuous_const
  · change Continuous (fun unit : Adelesˣ => Matrix.scalar (Fin 2) unit.inv)
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    by_cases equality : row = column
    · simpa only [Matrix.scalar_apply, Matrix.diagonal_apply, equality, ite_true,
        Units.inv_eq_val_inv] using
        Units.continuous_coe_inv (M := Adeles)
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply, equality, ite_false]
      exact continuous_const

theorem continuous {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) : Continuous data.centralCharacter := by
  obtain ⟨vector, argument, nonzero⟩ :=
    BinaryCentralCharacter.exists_realization_nonzero data cohomological
  have continuous : Continuous (fun unit : Adelesˣ =>
      data.realize vector (GeneralLinearGroup.scalar (Fin 2) unit * argument) /
        data.realize vector argument) :=
    ((CuspRealization.scalar_continuous data vector).comp
      (scalar_continuous.mul continuous_const)).div_const _
  convert continuous using 1
  funext unit
  rw [data.central, mul_div_cancel_right₀ _ nonzero]

theorem rational {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) (unit : ℚˣ) :
    data.centralCharacter (Units.map rationalAdele unit) = 1 := by
  obtain ⟨vector, argument, nonzero⟩ :=
    BinaryCentralCharacter.exists_realization_nonzero data cohomological
  have equality := data.leftRational (GeneralLinearGroup.scalar (Fin 2) unit) vector argument
  rw [GeneralLinearGroup.map_scalar, data.central] at equality
  exact (mul_left_inj' nonzero).mp (equality.trans (one_mul _).symm)

/-- The cusp central character satisfies the same analytic and arithmetic character
conditions used for the independent rank-one inducing character. -/
def rankOne {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) : RankOneCharacter where
  toMonoidHom := data.centralCharacter
  continuous := continuous data cohomological
  unitary := data.centralUnitary
  rational := rational data cohomological
  positiveReal := BinaryCentralCharacter.centralCharacter_positive data cohomological

theorem smoothAction_central (data : CuspidalRepresentation) (unit : Adelesˣ)
    (vector : data.smooth) :
    CuspRealization.smoothAction data (GeneralLinearGroup.scalar (Fin 2) unit) vector =
      data.centralCharacter unit • vector := by
  apply data.injective
  funext argument
  rw [CuspRealization.realize_equivariant, ← GeneralLinearGroup.scalar_commute,
    data.central, map_smul]
  rfl

theorem smoothAction_positive {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) (unit : ℝˣ) (positive : 0 < unit.val)
    (vector : data.smooth) :
    CuspRealization.smoothAction data
      (atInfinity (GeneralLinearGroup.scalar (Fin 2) unit)) vector = vector := by
  rw [BinaryCentralCharacter.atInfinity_scalar, smoothAction_central,
    BinaryCentralCharacter.centralCharacter_positive data cohomological unit positive, one_smul]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspCentralCharacter
