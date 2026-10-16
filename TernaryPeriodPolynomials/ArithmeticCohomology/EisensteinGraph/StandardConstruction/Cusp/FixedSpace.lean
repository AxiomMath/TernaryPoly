module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.CommonLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.Jets
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspFixedSpace

def fixed (data : CuspidalRepresentation) (subgroup : Subgroup BinaryFiniteGL) :
    Submodule ℂ data.H where
  carrier := {vector | ∀ unit : subgroup, data.π (atFinite unit.val) vector = vector}
  zero_mem' := by intro unit; exact map_zero _
  add_mem' {first second} firstFixed secondFixed := by
    intro unit
    rw [map_add, firstFixed unit, secondFixed unit]
  smul_mem' scalar vector vectorFixed := by
    intro unit
    rw [map_smul, vectorFixed unit]

theorem fixed_closed (data : CuspidalRepresentation) (subgroup : Subgroup BinaryFiniteGL) :
    IsClosed (fixed data subgroup : Set data.H) := by
  have equality : (fixed data subgroup : Set data.H) =
      ⋂ unit : subgroup, {vector | data.π (atFinite unit.val) vector = vector} := by
    ext vector
    simp [fixed]
  rw [equality]
  exact isClosed_iInter (fun unit =>
    isClosed_eq (CuspHilbertAction.continuous_vector data (atFinite unit.val)) continuous_id)

instance fixed_complete (data : CuspidalRepresentation) (subgroup : Subgroup BinaryFiniteGL) :
    CompleteSpace (fixed data subgroup) :=
  (fixed_closed data subgroup).isComplete.completeSpace_coe

theorem binary_finite_real_commute (finite : BinaryFiniteGL) (real : BinaryRealGL) :
    atFinite finite * atInfinity real = atInfinity real * atFinite finite := by
  apply CuspRealization.binary_ext
  · simp only [map_mul, CuspRealization.binaryReal_atFinite,
      CuspRealization.binaryReal_atInfinity, one_mul, mul_one]
  · simp only [map_mul, CuspRealization.binaryFinite_atFinite,
      CuspRealization.binaryFinite_atInfinity, one_mul, mul_one]

theorem fixed_real_stable (data : CuspidalRepresentation) (subgroup : Subgroup BinaryFiniteGL)
    (real : BinaryRealGL) (vector : data.H) (membership : vector ∈ fixed data subgroup) :
    data.π (atInfinity real) vector ∈ fixed data subgroup := by
  intro unit
  change (data.π (atFinite unit.val) * data.π (atInfinity real)) vector = _
  rw [← map_mul, binary_finite_real_commute, map_mul, Module.End.mul_apply, membership unit]

def compactRealLift {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (compact : AdelicGL) (membership : inMaximalCompact compact) :
    (Fin 1 → RealGL3) → fixed data.cusp CuspCommonLevel.principal :=
  fun real => ⟨(CuspLift.vector data .plane parameter function induced
    (compact * atInfinity (real 0))).val,
      CuspCommonLevel.compact_real_vector_fixed data parameter function induced compact membership (real 0)⟩

theorem compactRealLift_smooth {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (compact : AdelicGL) (membership : inMaximalCompact compact) :
    Smooth (compactRealLift data parameter function induced compact membership) := by
  let projection := (fixed data.cusp CuspCommonLevel.principal).orthogonalProjectionOnto.restrictScalars ℝ
  have composed := projection.contDiff.comp_contDiffOn
    (CuspLift.real_smooth data .plane parameter function induced compact)
  have agrees (real : Fin 1 → RealGL3) :
      projection (CuspLift.vector data .plane parameter function induced
        (compact * atInfinity (real 0))).val =
        compactRealLift data parameter function induced compact membership real :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (compactRealLift data parameter function induced compact membership real)
  unfold Smooth
  convert composed using 1
  funext matrices
  exact (agrees (fun index => invertibleMatrix (matrices index))).symm

theorem compactRealLift_jets_bounded {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (compact : AdelicGL) (membership : inMaximalCompact compact)
    (set : Set (Fin 1 → RealGL3)) (setCompact : IsCompact set) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ real ∈ set, ∀ derivative ≤ order,
      ‖SmoothJets.jet derivative
        (compactRealLift data parameter function induced compact membership) real‖ ≤ bound :=
  SmoothJets.finite_jets_bounded _
    (compactRealLift_smooth data parameter function induced compact membership) order set setCompact

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspFixedSpace
