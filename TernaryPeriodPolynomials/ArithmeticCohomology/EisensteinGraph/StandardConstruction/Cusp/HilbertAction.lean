module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.CentralCharacter

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspHilbertAction

def isometry (data : CuspidalRepresentation) (element : BinaryAdelicGL) :
    data.H →ₗᵢ[ℂ] data.H where
  toLinearMap := data.π element
  norm_map' := data.unitary element

theorem continuous_vector (data : CuspidalRepresentation) (element : BinaryAdelicGL) :
    Continuous (data.π element) := (isometry data element).continuous

theorem joint_continuous (data : CuspidalRepresentation) :
    Continuous (fun pair : BinaryAdelicGL × data.H => data.π pair.1 pair.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun element => (isometry data element).isometry.lipschitzWith) data.continuous

/-- Irreducibility makes every nonzero invariant linear subspace dense. -/
theorem invariant_dense (data : CuspidalRepresentation) (subspace : Submodule ℂ data.H)
    (stable : ∀ element vector, vector ∈ subspace → data.π element vector ∈ subspace)
    (nonzero : subspace ≠ ⊥) : Dense (subspace : Set data.H) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have closureStable : ∀ element vector, vector ∈ subspace.topologicalClosure →
      data.π element vector ∈ subspace.topologicalClosure := by
    intro element
    exact (Set.MapsTo.closure (stable element) (continuous_vector data element))
  rcases data.irreducible subspace.topologicalClosure subspace.isClosed_topologicalClosure
      closureStable with zero | top
  · exact False.elim (nonzero (bot_unique (zero ▸ subspace.le_topologicalClosure)))
  · exact top

theorem smooth_ne_bot {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) : data.smooth ≠ ⊥ := by
  obtain ⟨vector, argument, nonzero⟩ :=
    BinaryCentralCharacter.exists_realization_nonzero data cohomological
  intro zero
  have vanishes : vector.val = 0 := by
    simpa only [zero, Submodule.mem_bot] using vector.property
  have vectorZero : vector = 0 := Subtype.ext vanishes
  rw [vectorZero, map_zero, Pi.zero_apply] at nonzero
  exact nonzero rfl

theorem smooth_dense {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) : Dense (data.smooth : Set data.H) :=
  invariant_dense data data.smooth data.smooth_stable (smooth_ne_bot data cohomological)

theorem central {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) (unit : Adelesˣ) (vector : data.H) :
    data.π (GeneralLinearGroup.scalar (Fin 2) unit) vector = data.centralCharacter unit • vector := by
  have equality := Continuous.ext_on (smooth_dense data cohomological)
    (continuous_vector data (GeneralLinearGroup.scalar (Fin 2) unit))
    (continuous_const.smul continuous_id) (fun vector membership =>
      congrArg Subtype.val (CuspCentralCharacter.smoothAction_central data unit ⟨vector, membership⟩))
  exact congrFun equality vector

theorem central_positive {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) (unit : ℝˣ) (positive : 0 < unit.val)
    (vector : data.H) :
    data.π (atInfinity (GeneralLinearGroup.scalar (Fin 2) unit)) vector = vector := by
  rw [BinaryCentralCharacter.atInfinity_scalar, central data cohomological,
    BinaryCentralCharacter.centralCharacter_positive data cohomological unit positive, one_smul]

theorem central_rational {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) (unit : ℚˣ) (vector : data.H) :
    data.π (GeneralLinearGroup.scalar (Fin 2) (Units.map rationalAdele unit)) vector = vector := by
  rw [central data cohomological, CuspCentralCharacter.rational data cohomological, one_smul]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspHilbertAction
