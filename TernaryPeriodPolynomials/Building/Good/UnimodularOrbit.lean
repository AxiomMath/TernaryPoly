module

public import TernaryPeriodPolynomials.Building.Good.IntegralFrames
public import TernaryPeriodPolynomials.Building.Good.ChainComplex
public import TernaryPeriodPolynomials.Building.Good.ApartmentEquivariance
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Group.Int.Units

@[expose] public section


/-! Normalized unimodular integral apartments are actual translates of the
identity apartment by the congruence subgroup K. -/

open scoped BigOperators
noncomputable section
namespace TernaryPoly.GoodUnimodularOrbit

open ModThreeGoodAction GoodLatticeReduction GoodIntegralFrames GoodBuilding

abbrev IntegralMatrix := Matrix (Fin 3) (Fin 3) ℤ

/-- The identity matrix is normalized column by column modulo three. -/
theorem identity_normalized : NormalizedColumns (1 : IntegralMatrix) := by
  intro j
  simp [Matrix.one_apply]

/-- The concrete reference apartment is formed by the three coordinate lines. -/
def referenceApartment : GoodChainComplex.Cycles :=
  frameApartment (1 : IntegralMatrix) identity_normalized

/-- Column normalization is precisely the defining fixed-row condition for K. -/
theorem normalizedColumns_iff_mem_K (g : IntegralGL) :
    NormalizedColumns g.val ↔ g ∈ ModThreeGoodAction.K := by
  rw [ModThreeGoodAction.mem_K]
  constructor
  · intro h
    funext j
    change (∑ i, (1 : ZMod 3) * (g.val i j : ZMod 3)) = 1
    simpa only [one_mul] using h j
  · intro h j
    have hj := congrFun h j
    change (∑ i, (1 : ZMod 3) * (g.val i j : ZMod 3)) = 1 at hj
    simpa only [one_mul] using hj

/-- The integral matrix of an actual K element has normalized columns. -/
theorem element_normalized (g : GoodBuilding.K) : NormalizedColumns g.val.val :=
  (normalizedColumns_iff_mem_K g.val).mpr g.property

/-- A normalized integral matrix of absolute determinant one gives a genuine K element. -/
def matrixElement (M : IntegralMatrix) (hM : NormalizedColumns M)
    (hdet : M.det.natAbs = 1) : GoodBuilding.K :=
  ⟨Matrix.nonsingInvUnit M (Int.isUnit_iff_natAbs_eq.mpr hdet),
    (normalizedColumns_iff_mem_K _).mp hM⟩

@[simp] theorem matrixElement_val (M : IntegralMatrix) (hM : NormalizedColumns M)
    (hdet : M.det.natAbs = 1) : (matrixElement M hM hdet).val.val = M := rfl

/-- Acting on a coordinate basis vector gives the corresponding actual matrix column. -/
theorem rationalRepresentation_identity_column (g : IntegralGL) (j : Fin 3) :
    rationalRepresentation g (rationalVector (fun i => (1 : IntegralMatrix) i j)) =
      rationalVector (fun i => g.val i j) := by
  rw [rationalRepresentation_apply]
  have h : rationalVector (fun i => (1 : IntegralMatrix) i j) = Pi.single j 1 := by
    ext i
    simp [rationalVector, Matrix.one_apply, Pi.single_apply]
  rw [h, Matrix.mulVec_single_one]
  rfl

/-- The actual K action sends each coordinate line to its corresponding column line. -/
theorem columnLine_action (g : GoodBuilding.K) (j : Fin 3) :
    lineAction g (columnLine (1 : IntegralMatrix) identity_normalized j) =
      columnLine g.val.val (element_normalized g) j := by
  apply Subtype.ext
  change (Submodule.span ℚ {rationalVector (fun i => (1 : IntegralMatrix) i j)}).map
      (rationalRepresentation g.val).toLinearMap =
    Submodule.span ℚ {rationalVector (fun i => g.val.val i j)}
  rw [Submodule.map_span, Set.image_singleton]
  exact congrArg (fun v : Space => Submodule.span ℚ {v})
    (rationalRepresentation_identity_column g.val j)

/-- A normalized unimodular frame has exactly the image coordinate lines of its K element. -/
theorem columnLine_matrixElement (M : IntegralMatrix) (hM : NormalizedColumns M)
    (hdet : M.det.natAbs = 1) (j : Fin 3) :
    columnLine M hM j =
      lineAction (matrixElement M hM hdet)
        (columnLine (1 : IntegralMatrix) identity_normalized j) :=
  (columnLine_action (matrixElement M hM hdet) j).symm

/-- The apartment of an actual K matrix is its translate of the reference apartment. -/
theorem frameApartment_val_eq_translate (g : GoodBuilding.K) :
    frameApartment g.val.val (element_normalized g) =
      GoodChainComplex.complex.cyclesAction g referenceApartment := by
  have h : GoodChainComplex.complex.cyclesAction g referenceApartment =
      GoodApartmentCycles.apartmentCycle Good
        (lineAction g (columnLine (1 : IntegralMatrix) identity_normalized 0))
        (lineAction g (columnLine (1 : IntegralMatrix) identity_normalized 1))
        (lineAction g (columnLine (1 : IntegralMatrix) identity_normalized 2)) := by
    apply Subtype.ext
    exact GoodApartmentCycles.apartmentChainEquiv_apartment Good
      (subspaceEquiv g) (ModThreeGoodAction.act_finrank g)
      (ModThreeGoodAction.good_act_iff g) _ _ _
  rw [columnLine_action, columnLine_action, columnLine_action] at h
  exact h.symm

/-- Every normalized unimodular frame apartment is a translate by its actual matrix element. -/
theorem frameApartment_eq_translate (M : IntegralMatrix) (hM : NormalizedColumns M)
    (hdet : M.det.natAbs = 1) :
    frameApartment M hM =
      GoodChainComplex.complex.cyclesAction (matrixElement M hM hdet) referenceApartment :=
  frameApartment_val_eq_translate (matrixElement M hM hdet)

/-- The orbit statement retains the actual integral matrix underlying the translator. -/
theorem exists_frameApartment_translate (M : IntegralMatrix) (hM : NormalizedColumns M)
    (hdet : M.det.natAbs = 1) :
    ∃ g : GoodBuilding.K, g.val.val = M ∧
      frameApartment M hM = GoodChainComplex.complex.cyclesAction g referenceApartment :=
  ⟨matrixElement M hM hdet, rfl, frameApartment_eq_translate M hM hdet⟩

end TernaryPoly.GoodUnimodularOrbit
