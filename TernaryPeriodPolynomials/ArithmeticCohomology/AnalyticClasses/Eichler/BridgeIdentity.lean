module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.BridgeAnalytic

@[expose] public section


/-!
# The pointwise Eichler normal form of the reconstructed binary cocycle

A tuple of smooth Hilbert vectors indexed by the weight basis of `Sym^{n+1}` realizes to a
function `GL₂(𝔸) → Sym^{n+1}`. Realization intertwines the Hilbert binary operators with the
pointwise cohomological action, recovers the values of a binary cuspidal cochain from its
Hilbert embedding, and turns the Hilbert Eichler period into the scalar Eichler period of the
weighted scalar realization. Applied to the reconstruction of a binary cocycle as its Hilbert
normal form plus the coboundary of a finite-level correction, this gives the pointwise identity
`original(A)(h) = N_F(A)(h) + (A · κ - κ)(h)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Set
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-! ### Realization of smooth tuples -/

open Classical in
/-- The realization of a Hilbert vector, set to zero off the smooth vectors. -/
def smoothRealize (cusp : CuspidalRepresentation) (vector : cusp.H) : BinaryAdelicGL → ℂ :=
  if member : vector ∈ cusp.smooth then cusp.realize ⟨vector, member⟩ else 0

theorem smoothRealize_of_mem (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    smoothRealize cusp vector.val = cusp.realize vector := by
  rw [smoothRealize, dite_eq_left vector.property]

theorem smoothRealize_add (cusp : CuspidalRepresentation) (first second : cusp.H)
    (first_smooth : first ∈ cusp.smooth) (second_smooth : second ∈ cusp.smooth) :
    smoothRealize cusp (first + second) =
      smoothRealize cusp first + smoothRealize cusp second := by
  rw [smoothRealize_of_mem cusp ⟨first + second, cusp.smooth.add_mem first_smooth second_smooth⟩,
    smoothRealize_of_mem cusp ⟨first, first_smooth⟩,
    smoothRealize_of_mem cusp ⟨second, second_smooth⟩, ← map_add]
  rfl

theorem smoothRealize_sub (cusp : CuspidalRepresentation) (first second : cusp.H)
    (first_smooth : first ∈ cusp.smooth) (second_smooth : second ∈ cusp.smooth) :
    smoothRealize cusp (first - second) =
      smoothRealize cusp first - smoothRealize cusp second := by
  rw [smoothRealize_of_mem cusp ⟨first - second, cusp.smooth.sub_mem first_smooth second_smooth⟩,
    smoothRealize_of_mem cusp ⟨first, first_smooth⟩,
    smoothRealize_of_mem cusp ⟨second, second_smooth⟩, ← map_sub]
  rfl

theorem smoothRealize_smul (cusp : CuspidalRepresentation) (scalar : ℂ) (vector : cusp.H)
    (smooth : vector ∈ cusp.smooth) :
    smoothRealize cusp (scalar • vector) = scalar • smoothRealize cusp vector := by
  rw [smoothRealize_of_mem cusp ⟨scalar • vector, cusp.smooth.smul_mem scalar smooth⟩,
    smoothRealize_of_mem cusp ⟨vector, smooth⟩, ← map_smul]
  rfl

/-- **The pointwise lift** `h ↦ Σ_j realize(X_j)(h) e_j` of a Hilbert tuple. -/
def hilbertLift (cusp : CuspidalRepresentation) (n : ℕ) (vectors : Fin (n + 2) → cusp.H)
    (h : BinaryAdelicGL) : Binary.HomogeneousPoly (n + 1) :=
  ∑ position, smoothRealize cusp (vectors position) h • binaryWeightBasis (n + 1) position

theorem coord_hilbertLift (cusp : CuspidalRepresentation) (vectors : Fin (n + 2) → cusp.H)
    (h : BinaryAdelicGL) (position : Fin (n + 2)) :
    (binaryWeightBasis (n + 1)).coord position (hilbertLift cusp n vectors h) =
      smoothRealize cusp (vectors position) h := by
  rw [Module.Basis.coord_apply, hilbertLift, Module.Basis.repr_sum_self]

theorem hilbertLift_ext (cusp : CuspidalRepresentation) (vectors : Fin (n + 2) → cusp.H)
    (h : BinaryAdelicGL) (value : Binary.HomogeneousPoly (n + 1))
    (coordinates : ∀ position, smoothRealize cusp (vectors position) h =
      (binaryWeightBasis (n + 1)).coord position value) :
    hilbertLift cusp n vectors h = value := by
  apply (binaryWeightBasis (n + 1)).ext_elem
  intro position
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply, coord_hilbertLift, coordinates]

theorem hilbertLift_add (cusp : CuspidalRepresentation) (first second : Fin (n + 2) → cusp.H)
    (first_smooth : ∀ position, first position ∈ cusp.smooth)
    (second_smooth : ∀ position, second position ∈ cusp.smooth) :
    hilbertLift cusp n (first + second) = hilbertLift cusp n first + hilbertLift cusp n second := by
  funext h
  apply hilbertLift_ext
  intro position
  rw [Pi.add_apply, Pi.add_apply, map_add, coord_hilbertLift, coord_hilbertLift,
    smoothRealize_add cusp _ _ (first_smooth position) (second_smooth position), Pi.add_apply]

theorem hilbertLift_smul (cusp : CuspidalRepresentation) (scalar : ℂ)
    (vectors : Fin (n + 2) → cusp.H) (smooth : ∀ position, vectors position ∈ cusp.smooth) :
    hilbertLift cusp n (scalar • vectors) = scalar • hilbertLift cusp n vectors := by
  funext h
  apply hilbertLift_ext
  intro position
  rw [Pi.smul_apply, Pi.smul_apply, map_smul, coord_hilbertLift,
    smoothRealize_smul cusp scalar _ (smooth position), Pi.smul_apply]

theorem hilbertLift_sub (cusp : CuspidalRepresentation) (first second : Fin (n + 2) → cusp.H)
    (first_smooth : ∀ position, first position ∈ cusp.smooth)
    (second_smooth : ∀ position, second position ∈ cusp.smooth) :
    hilbertLift cusp n (first - second) = hilbertLift cusp n first - hilbertLift cusp n second := by
  funext h
  apply hilbertLift_ext
  intro position
  rw [Pi.sub_apply, Pi.sub_apply, map_sub, coord_hilbertLift, coord_hilbertLift,
    smoothRealize_sub cusp _ _ (first_smooth position) (second_smooth position), Pi.sub_apply]

/-! ### Realization intertwines the Hilbert binary operators -/

theorem binaryHilbertOperator_smooth (cusp : CuspidalRepresentation) (A : BinaryRealGL)
    (vectors : Fin (n + 2) → cusp.H) (smooth : ∀ position, vectors position ∈ cusp.smooth)
    (position : Fin (n + 2)) :
    binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) A vectors position ∈ cusp.smooth := by
  rw [binaryHilbertOperator_apply]
  exact cusp.smooth.smul_mem _ (cusp.smooth.sum_mem fun source _ =>
    cusp.smooth.smul_mem _ (cusp.smooth_stable _ _ (smooth source)))

theorem smoothRealize_binaryHilbertOperator (cusp : CuspidalRepresentation) (A : BinaryRealGL)
    (vectors : Fin (n + 2) → cusp.H) (smooth : ∀ position, vectors position ∈ cusp.smooth)
    (position : Fin (n + 2)) (h : BinaryAdelicGL) :
    smoothRealize cusp (binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) A vectors position)
        h =
      normPower (Matrix.GeneralLinearGroup.det (atInfinity A)) (((n : ℂ) + 3) / 2) *
        ∑ source, (binaryWeightBasis (n + 1)).coord position
          (binaryCoefficient n A (binaryWeightBasis (n + 1) source)) *
          smoothRealize cusp (vectors source) (h * atInfinity A) := by
  let translated (source : Fin (n + 2)) : cusp.smooth :=
    ⟨cusp.π (atInfinity A) (vectors source), cusp.smooth_stable _ _ (smooth source)⟩
  let combined : cusp.smooth :=
    normPower (Matrix.GeneralLinearGroup.det (atInfinity A)) (((n : ℂ) + 3) / 2) •
      ∑ source, (binaryWeightBasis (n + 1)).coord position
        (binaryCoefficient n A (binaryWeightBasis (n + 1) source)) • translated source
  have value : combined.val =
      binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) A vectors position := by
    rw [binaryHilbertOperator_apply]
    simp only [combined, translated, Submodule.coe_smul, Submodule.coe_sum]
  rw [← value, smoothRealize_of_mem]
  simp only [combined, map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro source _
  rw [smoothRealize_of_mem cusp ⟨_, smooth source⟩]
  exact congrArg _ (cusp.equivariant (atInfinity A) ⟨_, smooth source⟩ h)

/-- **Realization intertwines the Hilbert binary operator with the pointwise action.** -/
theorem hilbertLift_binaryHilbertOperator (cusp : CuspidalRepresentation) (A : BinaryRealGL)
    (vectors : Fin (n + 2) → cusp.H) (smooth : ∀ position, vectors position ∈ cusp.smooth) :
    hilbertLift cusp n (binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) A vectors) =
      binaryAmbientRepresentation n A (hilbertLift cusp n vectors) := by
  funext h
  apply hilbertLift_ext
  intro position
  rw [smoothRealize_binaryHilbertOperator cusp A vectors smooth position h]
  change _ = (binaryWeightBasis (n + 1)).coord position
    (normPower (Matrix.GeneralLinearGroup.det (atInfinity A)) (((n : ℂ) + 3) / 2) •
      binaryCoefficient n A (hilbertLift cusp n vectors (h * atInfinity A)))
  rw [map_smul, smul_eq_mul, hilbertLift, map_sum, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro source _
  rw [map_smul, map_smul, smul_eq_mul, mul_comm]

/-! ### Realization of the Hilbert embedding and of the Eichler period -/

theorem binaryHilbertEmbedding_smooth (cusp : CuspidalRepresentation)
    (values : binaryCuspidalValues cusp n) (position : Fin (n + 2)) :
    binaryHilbertEmbedding cusp (binaryWeightBasis (n + 1)) values position ∈ cusp.smooth :=
  (binarySmoothCoordinates cusp (binaryWeightBasis (n + 1)) values position).property

/-- **Realization recovers the values of a binary cuspidal cochain.** -/
theorem hilbertLift_binaryHilbertEmbedding (cusp : CuspidalRepresentation)
    (values : binaryCuspidalValues cusp n) :
    hilbertLift cusp n (binaryHilbertEmbedding cusp (binaryWeightBasis (n + 1)) values) =
      values.val := by
  funext h
  apply hilbertLift_ext
  intro position
  change smoothRealize cusp
    (binarySmoothCoordinate cusp ((binaryWeightBasis (n + 1)).coord position) values).val h = _
  rw [smoothRealize_of_mem, binarySmoothCoordinate_realize]

theorem binaryEndpointPeriod_smooth (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (halfWeight : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (z : ℂ) (positive : 0 < z.im) (position : Fin (n + 2)) :
    binaryEndpointPeriod cusp n halfWeight vector.val z position ∈ cusp.smooth := by
  obtain ⟨w, value, _⟩ :=
    binaryEndpointPeriod_realize cusp stages n halfWeight vector fixed z positive position
  rw [← value]
  exact w.property

/-- **Realization turns the Hilbert Eichler period into the scalar Eichler period.** -/
theorem hilbertLift_binaryEndpointPeriod (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (halfWeight : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (z : ℂ) (positive : 0 < z.im) :
    hilbertLift cusp n (binaryEndpointPeriod cusp n halfWeight vector.val z) =
      eichlerPeriod n (cuspScalarWeightedRealization cusp halfWeight vector) z := by
  funext h
  apply hilbertLift_ext
  intro position
  obtain ⟨w, value, realization⟩ :=
    binaryEndpointPeriod_realize cusp stages n halfWeight vector fixed z positive position
  rw [eichlerPeriod, Module.Basis.coord_apply, Module.Basis.repr_sum_self, ← value,
    smoothRealize_of_mem, realization]
  apply intervalIntegral.integral_congr
  intro t member
  have path : clampedPath z t = eichlerPath z t := clampedPath_eqOn z member
  simp only [endpointCoefficient, eichlerIntegrand, path, cuspScalarWeightedRealization,
    cuspScalarAffineRealization, Complex.real_smul]
  ring

/-! ### The pointwise identity -/

/-- The scalar weighted realization of the classical endpoint vector. -/
abbrev endpointScalar (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth) :
    BinaryAdelicGL → ℂ → ℂ :=
  cuspScalarWeightedRealization cusp halfWeight vector

/-- **The reconstructed binary cocycle is the pointwise Eichler normal form plus a
coboundary.** -/
theorem original_eq_eichlerNormal_add_of_smooth (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (halfWeight : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp n))
    (correction : Fin (n + 2) → cusp.H)
    (correction_smooth : ∀ position, correction position ∈ cusp.smooth)
    (reconstruction : ∀ A : BinaryRealGL,
      binaryHilbertEmbedding cusp (binaryWeightBasis (n + 1)) (original A) =
        (2 : ℂ)⁻¹ • (binaryEndpointPeriod cusp n halfWeight vector.val
          ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
          binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) UpperHalfPlane.J
            (binaryEndpointPeriod cusp n halfWeight vector.val
              (binaryComplexReflection ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)))) +
        (binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) A correction - correction))
    (A : BinaryRealGL) (h : BinaryAdelicGL) :
    (original A).val h = eichlerNormal n (endpointScalar cusp halfWeight vector) A h +
      (binaryAmbientRepresentation n A (hilbertLift cusp n correction) h -
        hilbertLift cusp n correction h) := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have first_smooth := binaryEndpointPeriod_smooth (n := n) cusp stages halfWeight vector fixed
    (basePoint A) positive
  have second_smooth := binaryEndpointPeriod_smooth (n := n) cusp stages halfWeight vector fixed
    (binaryComplexReflection (basePoint A)) reflected_positive
  have third_smooth := binaryHilbertOperator_smooth cusp UpperHalfPlane.J _ second_smooth
  have operator_smooth := binaryHilbertOperator_smooth cusp A correction correction_smooth
  have sum_smooth : ∀ position, (binaryEndpointPeriod cusp n halfWeight vector.val (basePoint A) +
      binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) UpperHalfPlane.J
        (binaryEndpointPeriod cusp n halfWeight vector.val
          (binaryComplexReflection (basePoint A)))) position ∈ cusp.smooth :=
    fun position => cusp.smooth.add_mem (first_smooth position) (third_smooth position)
  have normal_smooth : ∀ position, ((2 : ℂ)⁻¹ • (binaryEndpointPeriod cusp n halfWeight
      vector.val (basePoint A) + binaryHilbertOperator cusp (binaryWeightBasis (n + 1))
        UpperHalfPlane.J (binaryEndpointPeriod cusp n halfWeight vector.val
          (binaryComplexReflection (basePoint A))))) position ∈ cusp.smooth :=
    fun position => cusp.smooth.smul_mem _ (sum_smooth position)
  have boundary_smooth : ∀ position,
      (binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) A correction - correction)
        position ∈ cusp.smooth :=
    fun position => cusp.smooth.sub_mem (operator_smooth position) (correction_smooth position)
  have identity : binaryHilbertEmbedding cusp (binaryWeightBasis (n + 1)) (original A) =
      (2 : ℂ)⁻¹ • (binaryEndpointPeriod cusp n halfWeight vector.val (basePoint A) +
        binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) UpperHalfPlane.J
          (binaryEndpointPeriod cusp n halfWeight vector.val
            (binaryComplexReflection (basePoint A)))) +
      (binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) A correction - correction) :=
    reconstruction A
  have embedded : hilbertLift cusp n
      (binaryHilbertEmbedding cusp (binaryWeightBasis (n + 1)) (original A)) = (original A).val :=
    hilbertLift_binaryHilbertEmbedding cusp (original A)
  have lifted := congrArg (hilbertLift cusp n) identity
  rw [embedded, hilbertLift_add cusp _ _ normal_smooth boundary_smooth,
    hilbertLift_smul cusp _ _ sum_smooth, hilbertLift_add cusp _ _ first_smooth third_smooth,
    hilbertLift_sub cusp _ _ operator_smooth correction_smooth,
    hilbertLift_binaryHilbertOperator cusp A correction correction_smooth,
    hilbertLift_binaryHilbertOperator cusp UpperHalfPlane.J _ second_smooth,
    hilbertLift_binaryEndpointPeriod cusp stages halfWeight vector fixed _ positive,
    hilbertLift_binaryEndpointPeriod cusp stages halfWeight vector fixed _ reflected_positive]
    at lifted
  rw [lifted]
  rfl

/-- **The pointwise identity for the reconstructed binary cocycle**, with the smoothness of
the correction derived from the analyticity of the Hilbert embedding. -/
theorem original_eq_eichlerNormal_add (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (halfWeight : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp n))
    (analytic : AnalyticAt ℝ (fun matrix : BinaryRealMatrix =>
      binaryHilbertEmbedding cusp (binaryWeightBasis (n + 1))
        (original (invertibleMatrix matrix))) 1)
    (correction : Fin (n + 2) → cusp.H) (level : Subgroup BinaryFiniteGL)
    (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (correction_fixed : ∀ element : level, ∀ position,
      cusp.π (atFinite element.val) (correction position) = correction position)
    (reconstruction : ∀ A : BinaryRealGL,
      binaryHilbertEmbedding cusp (binaryWeightBasis (n + 1)) (original A) =
        (2 : ℂ)⁻¹ • (binaryEndpointPeriod cusp n halfWeight vector.val
          ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
          binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) UpperHalfPlane.J
            (binaryEndpointPeriod cusp n halfWeight vector.val
              (binaryComplexReflection ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)))) +
        (binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) A correction - correction))
    (A : BinaryRealGL) (h : BinaryAdelicGL) :
    (original A).val h = eichlerNormal n (endpointScalar cusp halfWeight vector) A h +
      (binaryAmbientRepresentation n A (hilbertLift cusp n correction) h -
        hilbertLift cusp n correction h) :=
  original_eq_eichlerNormal_add_of_smooth cusp stages halfWeight vector fixed original correction
    (correction_smooth cusp halfWeight vector original analytic correction level level_open
      level_compact correction_fixed reconstruction) reconstruction A h

end TernaryPeriodPolynomials.AnalyticClasses
