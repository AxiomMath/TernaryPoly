module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.TensorAction
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspUnitaryOperator (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    cusp.H →L[ℂ] cusp.H :=
  (cusp.π matrix).mkContinuous 1 (fun vector => by
    rw [cusp.unitary, one_mul])

theorem cuspUnitaryOperator_apply (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL)
    (vector : cusp.H) : cuspUnitaryOperator cusp matrix vector = cusp.π matrix vector := rfl

theorem sphericalCusp_smooth_dense (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) : Dense (cusp.smooth : Set cusp.H) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have stable : ∀ matrix vector, vector ∈ cusp.smooth.topologicalClosure →
      cusp.π matrix vector ∈ cusp.smooth.topologicalClosure := by
    intro matrix vector member
    have original : cusp.smooth.map (cusp.π matrix) ≤ cusp.smooth := by
      rintro _ ⟨original, original_mem, rfl⟩
      exact cusp.smooth_stable matrix original original_mem
    have closure_map := (Submodule.topologicalClosure_map
      (cuspUnitaryOperator cusp matrix) cusp.smooth).trans
      (Submodule.topologicalClosure_mono original)
    exact closure_map ⟨vector, member, rfl⟩
  rcases cusp.irreducible cusp.smooth.topologicalClosure isClosed_closure stable with zero | full
  · rcases spherical with ⟨vector, nonzero, _⟩
    have member : vector.val ∈ cusp.smooth.topologicalClosure :=
      subset_closure vector.property
    rw [zero, Submodule.mem_bot] at member
    exact False.elim (nonzero (Subtype.ext member))
  · exact full

variable {degree : ℕ} {index : Type} [Fintype index]

def binaryHilbertOperator (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (matrix : BinaryRealGL) : (index → cusp.H) →L[ℂ] (index → cusp.H) :=
  normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
    ContinuousLinearMap.pi (fun position =>
      ∑ source, basis.coord position (binaryCoefficient degree matrix (basis source)) •
        (cuspUnitaryOperator cusp (atInfinity matrix)).comp (ContinuousLinearMap.proj source))

theorem binaryHilbertOperator_apply (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (matrix : BinaryRealGL) (vectors : index → cusp.H) (position : index) :
    binaryHilbertOperator cusp basis matrix vectors position =
      normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
        ∑ source, basis.coord position (binaryCoefficient degree matrix (basis source)) •
          cusp.π (atInfinity matrix) (vectors source) := by
  simp only [binaryHilbertOperator, smul_apply, ContinuousLinearMap.pi_apply,
    sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Pi.smul_apply, cuspUnitaryOperator_apply]

def binaryHilbertEmbedding (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    binaryCuspidalValues cusp degree →ₗ[ℂ] (index → cusp.H) where
  toFun values position := (binarySmoothCoordinates cusp basis values position).val
  map_add' first second := by
    funext position
    exact congrArg Subtype.val (congrFun (map_add (binarySmoothCoordinates cusp basis) first second) position)
  map_smul' scalar values := by
    funext position
    exact congrArg Subtype.val (congrFun (map_smul (binarySmoothCoordinates cusp basis) scalar values) position)

omit [Fintype index] in
theorem binaryHilbertEmbedding_injective (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    Function.Injective (binaryHilbertEmbedding cusp basis) := by
  intro first second equality
  apply binarySmoothCoordinates_injective cusp basis
  funext position
  apply Subtype.ext
  exact congrFun equality position

theorem binaryHilbertOperator_intertwines (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (matrix : BinaryRealGL) (values : binaryCuspidalValues cusp degree) :
    binaryHilbertOperator cusp basis matrix (binaryHilbertEmbedding cusp basis values) =
      binaryHilbertEmbedding cusp basis (binaryCuspidalRepresentation cusp degree matrix values) := by
  funext position
  have equality := congrArg Subtype.val (binarySmoothCoordinates_action cusp basis matrix values position)
  simpa only [binaryHilbertOperator_apply, binaryHilbertEmbedding, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.coe_smul, Submodule.coe_sum, cuspSmoothAction] using equality.symm

def binaryHilbertTranslation (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    (index → cusp.H) →L[ℂ] (index → cusp.H) :=
  ContinuousLinearMap.piMap (fun _ => cuspUnitaryOperator cusp matrix)

omit [Fintype index] in
theorem binaryHilbertTranslation_apply (cusp : CuspidalRepresentation)
    (matrix : BinaryAdelicGL) (vectors : index → cusp.H) (position : index) :
    binaryHilbertTranslation cusp matrix vectors position = cusp.π matrix (vectors position) := rfl

omit [Fintype index] in
theorem binaryHilbertTranslation_intertwines (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (matrix : BinaryAdelicGL) (values : binaryCuspidalValues cusp degree) :
    binaryHilbertTranslation cusp matrix (binaryHilbertEmbedding cusp basis values) =
      binaryHilbertEmbedding cusp basis (binaryRightTranslation cusp degree matrix values) := by
  funext position
  exact (congrArg Subtype.val
    (binarySmoothCoordinate_right_translate cusp (basis.coord position) values matrix)).symm

theorem binaryHilbertOperator_preserves_finiteLevel (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (matrix : BinaryRealGL) (element : BinaryFiniteGL) (vector : index → cusp.H)
    (fixed : ∀ position, cusp.π (atFinite element) (vector position) = vector position)
    (position : index) :
    cusp.π (atFinite element) (binaryHilbertOperator cusp basis matrix vector position) =
      binaryHilbertOperator cusp basis matrix vector position := by
  rw [binaryHilbertOperator_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro source _
  rw [map_smul]
  congr 1
  change (cusp.π (atFinite element) * cusp.π (atInfinity matrix)) (vector source) = _
  rw [← map_mul, (atInfinity_commute_atFinite matrix element).symm.eq,
    map_mul, Module.End.mul_apply, fixed]

theorem binaryHilbertEmbedding_dense (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    DenseRange (binaryHilbertEmbedding cusp basis) := by
  have dense : DenseRange (fun vectors : index → cusp.smooth =>
      fun position => (vectors position).val) :=
    DenseRange.piMap (fun _ =>
      denseRange_subtype_val.mpr (sphericalCusp_smooth_dense cusp spherical))
  have ranges : Set.range (binaryHilbertEmbedding cusp basis) =
      Set.range (fun vectors : index → cusp.smooth => fun position => (vectors position).val) := by
    ext vectors
    constructor
    · rintro ⟨values, rfl⟩
      exact ⟨binarySmoothCoordinates cusp basis values, rfl⟩
    · rintro ⟨smooth_vectors, rfl⟩
      obtain ⟨values, coordinates⟩ := binarySmoothCoordinates_surjective cusp basis smooth_vectors
      refine ⟨values, ?_⟩
      change (fun position => (binarySmoothCoordinates cusp basis values position).val) = _
      rw [coordinates]
  change Dense (Set.range (binaryHilbertEmbedding cusp basis))
  rw [ranges]
  exact dense

theorem binaryHilbertOperator_one (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    binaryHilbertOperator cusp basis 1 = ContinuousLinearMap.id ℂ (index → cusp.H) := by
  apply DFunLike.coe_injective
  apply (binaryHilbertEmbedding_dense cusp spherical basis).equalizer
    (binaryHilbertOperator cusp basis 1).continuous continuous_id
  funext values
  change binaryHilbertOperator cusp basis 1 (binaryHilbertEmbedding cusp basis values) = _
  rw [binaryHilbertOperator_intertwines, map_one]
  rfl

theorem binaryHilbertOperator_mul (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (first second : BinaryRealGL) :
    binaryHilbertOperator cusp basis (first * second) =
      (binaryHilbertOperator cusp basis first).comp (binaryHilbertOperator cusp basis second) := by
  apply DFunLike.coe_injective
  apply (binaryHilbertEmbedding_dense cusp spherical basis).equalizer
    (binaryHilbertOperator cusp basis (first * second)).continuous
    ((binaryHilbertOperator cusp basis first).continuous.comp
      (binaryHilbertOperator cusp basis second).continuous)
  funext values
  change binaryHilbertOperator cusp basis (first * second) (binaryHilbertEmbedding cusp basis values) =
    binaryHilbertOperator cusp basis first
      (binaryHilbertOperator cusp basis second (binaryHilbertEmbedding cusp basis values))
  rw [binaryHilbertOperator_intertwines, binaryHilbertOperator_intertwines,
    binaryHilbertOperator_intertwines, map_mul]
  rfl

def binaryHilbertRepresentation (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    Representation ℂ BinaryRealGL (index → cusp.H) where
  toFun matrix := (binaryHilbertOperator cusp basis matrix).toLinearMap
  map_one' := congrArg ContinuousLinearMap.toLinearMap (binaryHilbertOperator_one cusp spherical basis)
  map_mul' first second := congrArg ContinuousLinearMap.toLinearMap
    (binaryHilbertOperator_mul cusp spherical basis first second)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
