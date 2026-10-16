module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.HilbertModel
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspUnitaryIsometryEquiv (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    cusp.H ≃ₗᵢ[ℂ] cusp.H where
  toLinearEquiv :=
    { toLinearMap := cusp.π matrix
      invFun := cusp.π matrix⁻¹
      left_inv := by
        intro vector
        change (cusp.π matrix⁻¹ * cusp.π matrix) vector = vector
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := by
        intro vector
        change (cusp.π matrix * cusp.π matrix⁻¹) vector = vector
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl }
  norm_map' := cusp.unitary matrix

def cuspSphericalValues (cusp : CuspidalRepresentation) : Submodule ℂ cusp.H where
  carrier := {vector | ∀ element : GeneralLinearGroup (Fin 2) IntegralAdeles,
    cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding element)) vector = vector}
  zero_mem' := by simp
  add_mem' first_fixed second_fixed := by
    intro element
    rw [map_add, first_fixed element, second_fixed element]
  smul_mem' scalar vector fixed := by
    intro element
    rw [map_smul, fixed element]

theorem cuspSphericalValues_closed (cusp : CuspidalRepresentation) :
    IsClosed (cuspSphericalValues cusp : Set cusp.H) := by
  change IsClosed {vector : cusp.H | ∀ element : GeneralLinearGroup (Fin 2) IntegralAdeles,
    cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding element)) vector = vector}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro element
  exact isClosed_eq (cuspUnitaryOperator cusp
    (atFinite (GeneralLinearGroup.map integralEmbedding element))).continuous continuous_id

instance cuspSphericalValues_completeSpace (cusp : CuspidalRepresentation) :
    CompleteSpace (cuspSphericalValues cusp) := by
  let : IsClosed (cuspSphericalValues cusp : Set cusp.H) := cuspSphericalValues_closed cusp
  infer_instance

def cuspSphericalProjection (cusp : CuspidalRepresentation) : cusp.H →L[ℂ] cusp.H :=
  (cuspSphericalValues cusp).starProjection

theorem cuspSphericalProjection_eq_self_iff (cusp : CuspidalRepresentation) (vector : cusp.H) :
    cuspSphericalProjection cusp vector = vector ↔ vector ∈ cuspSphericalValues cusp :=
  Submodule.starProjection_eq_self_iff

theorem cuspSphericalProjection_mem (cusp : CuspidalRepresentation) (vector : cusp.H) :
    cuspSphericalProjection cusp vector ∈ cuspSphericalValues cusp := by
  change (cuspSphericalValues cusp).starProjection vector ∈ cuspSphericalValues cusp
  have member : (cuspSphericalValues cusp).starProjection vector ∈
      (cuspSphericalValues cusp).starProjection.toLinearMap.range := ⟨vector, rfl⟩
  rwa [Submodule.range_starProjection] at member

theorem cuspSphericalProjection_ne_zero (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) : cuspSphericalProjection cusp ≠ 0 := by
  intro zero
  obtain ⟨vector, nonzero, fixed⟩ := spherical
  have identity := (cuspSphericalProjection_eq_self_iff cusp vector.val).mpr fixed
  rw [zero, _root_.zero_apply] at identity
  exact nonzero (Subtype.ext identity.symm)

theorem cuspSphericalValues_real_stable (cusp : CuspidalRepresentation)
    (matrix : BinaryRealGL) (vector : cusp.H) (fixed : vector ∈ cuspSphericalValues cusp) :
    cusp.π (atInfinity matrix) vector ∈ cuspSphericalValues cusp := by
  intro element
  change (cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding element)) *
    cusp.π (atInfinity matrix)) vector = _
  rw [← map_mul, (atInfinity_commute_atFinite matrix
    (GeneralLinearGroup.map integralEmbedding element)).symm.eq, map_mul, Module.End.mul_apply,
    fixed element]

theorem cuspSphericalValues_real_map (cusp : CuspidalRepresentation) (matrix : BinaryRealGL) :
    (cuspSphericalValues cusp).map (cusp.π (atInfinity matrix)) = cuspSphericalValues cusp := by
  apply le_antisymm
  · rintro _ ⟨vector, fixed, rfl⟩
    exact cuspSphericalValues_real_stable cusp matrix vector fixed
  · intro vector fixed
    refine ⟨cusp.π (atInfinity matrix⁻¹) vector,
      cuspSphericalValues_real_stable cusp matrix⁻¹ vector fixed, ?_⟩
    change (cusp.π (atInfinity matrix) * cusp.π (atInfinity matrix⁻¹)) vector = vector
    rw [← map_mul, ← atInfinity_mul, mul_inv_cancel, atInfinity_one, map_one]
    rfl

theorem cuspSphericalProjection_real (cusp : CuspidalRepresentation)
    (matrix : BinaryRealGL) (vector : cusp.H) :
    cuspSphericalProjection cusp (cusp.π (atInfinity matrix) vector) =
      cusp.π (atInfinity matrix) (cuspSphericalProjection cusp vector) := by
  have naturality := Submodule.starProjection_map_apply
    (cuspUnitaryIsometryEquiv cusp (atInfinity matrix)) (cuspSphericalValues cusp)
    (cuspUnitaryIsometryEquiv cusp (atInfinity matrix) vector)
  rw [LinearIsometryEquiv.symm_apply_apply] at naturality
  have map_eq : (cuspSphericalValues cusp).map
      (cuspUnitaryIsometryEquiv cusp (atInfinity matrix)).toLinearEquiv.toLinearMap =
      cuspSphericalValues cusp := cuspSphericalValues_real_map cusp matrix
  simp only [map_eq] at naturality
  exact naturality

theorem cusp_exists_translate_detected {target : Type*} [NormedAddCommGroup target]
    [NormedSpace ℂ target] (cusp : CuspidalRepresentation)
    (operator : cusp.H →L[ℂ] target) (operator_nonzero : operator ≠ 0)
    (vector : cusp.H) (vector_nonzero : vector ≠ 0) :
    ∃ matrix : BinaryAdelicGL, operator (cusp.π matrix vector) ≠ 0 := by
  let kernel : Submodule ℂ cusp.H :=
    { carrier := {value | ∀ matrix : BinaryAdelicGL, operator (cusp.π matrix value) = 0}
      zero_mem' := by simp
      add_mem' := by
        intro first second first_zero second_zero matrix
        rw [map_add, map_add, first_zero matrix, second_zero matrix, add_zero]
      smul_mem' := by
        intro scalar value zero matrix
        rw [map_smul, map_smul, zero matrix, smul_zero] }
  have closed : IsClosed (kernel : Set cusp.H) := by
    change IsClosed {value : cusp.H | ∀ matrix : BinaryAdelicGL,
      operator (cusp.π matrix value) = 0}
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro matrix
    exact isClosed_eq (operator.continuous.comp (cuspUnitaryOperator cusp matrix).continuous)
      continuous_const
  have stable : ∀ matrix value, value ∈ kernel → cusp.π matrix value ∈ kernel := by
    intro matrix value zero other
    change operator ((cusp.π other * cusp.π matrix) value) = 0
    rw [← map_mul]
    exact zero (other * matrix)
  by_contra all_zero
  push Not at all_zero
  rcases cusp.irreducible kernel closed stable with zero | full
  · have member : vector ∈ kernel := all_zero
    rw [zero, Submodule.mem_bot] at member
    exact vector_nonzero member
  · apply operator_nonzero
    ext value
    have member : value ∈ kernel := full ▸ Submodule.mem_top
    have zero := member 1
    simpa only [map_one, Module.End.one_apply, _root_.zero_apply] using zero

theorem binaryAdelic_exists_real_finite (matrix : BinaryAdelicGL) :
    ∃ (real : BinaryRealGL) (finite : BinaryFiniteGL),
      matrix = atInfinity real * atFinite finite := by
  refine ⟨GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) matrix,
    GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) matrix, ?_⟩
  apply Units.ext
  funext row column
  apply Prod.ext
  · simp only [atInfinity, atFinite, combineGL, pairMatrix, GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Prod.fst_sum, Prod.fst_mul, GeneralLinearGroup.coe_one]
    simp only [← Matrix.mul_apply, mul_one]
    rfl
  · simp only [atInfinity, atFinite, combineGL, pairMatrix, GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Prod.snd_sum, Prod.snd_mul, GeneralLinearGroup.coe_one]
    simp only [← Matrix.mul_apply, one_mul]
    rfl

theorem cuspSphericalProjection_finite_nonzero (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (vector : cusp.H) (nonzero : vector ≠ 0) :
    ∃ finite : BinaryFiniteGL,
      cuspSphericalProjection cusp (cusp.π (atFinite finite) vector) ≠ 0 := by
  obtain ⟨matrix, detected⟩ := cusp_exists_translate_detected cusp
    (cuspSphericalProjection cusp) (cuspSphericalProjection_ne_zero cusp spherical) vector nonzero
  obtain ⟨real, finite, decomposition⟩ := binaryAdelic_exists_real_finite matrix
  refine ⟨finite, ?_⟩
  intro zero
  apply detected
  rw [decomposition, map_mul, Module.End.mul_apply, cuspSphericalProjection_real, zero, map_zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
