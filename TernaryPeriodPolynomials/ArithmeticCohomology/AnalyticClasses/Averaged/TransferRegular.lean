module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.BridgeTransferIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.CanonicalTransferGlueAverage

@[expose] public section


/-!
# Regularity of a binary family that is an Eichler normal form plus a coboundary

Let `κ : GL₂(𝔸) → Sym^{n+1}` have uniformly bounded scalar tests. A scalar test of the
translate `A · κ` at `h` is `‖det A‖^{(n+3)/2} Σⱼ κⱼ(h A) λ(A · eⱼ)`, whose factors depending on
`A` are continuous; hence it is bounded on compact sets of matrices, uniformly in `h`. Therefore
a binary family `N(A) = N_F(A) + (A · κ - κ)`, with `N_F` the pointwise Eichler normal form of
the scalar weighted realization of a smooth vector and `κ` the lift of a smooth tuple, is regular:
its scalar tests are continuous in `A` and bounded on compact sets uniformly in the adelic point.
This applies to the binary values of the canonical relative cocycle once they are so decomposed.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ} {index : Type} [Fintype index]

/-! ### Bounds for the translates -/

/-- A scalar test of a translate in the weight basis. -/
theorem functional_binaryAmbientRepresentation (A : BinaryRealGL)
    (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) (h : BinaryAdelicGL)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    functional (binaryAmbientRepresentation n A κ h) =
      normPower (GeneralLinearGroup.det (atInfinity A)) (((n : ℂ) + 3) / 2) *
        ∑ position, (binaryWeightBasis (n + 1)).coord position (κ (h * atInfinity A)) *
          functional (binaryCoefficient n A (binaryWeightBasis (n + 1) position)) := by
  change functional (normPower (GeneralLinearGroup.det (atInfinity A)) (((n : ℂ) + 3) / 2) •
    binaryCoefficient n A (κ (h * atInfinity A))) = _
  rw [map_smul, smul_eq_mul]
  exact congrArg _ (functional_eq_sum_coord (functional ∘ₗ binaryCoefficient n A) _)

theorem normPower_det_atInfinity_continuous :
    Continuous (fun A : BinaryRealGL =>
      normPower (GeneralLinearGroup.det (atInfinity A)) (((n : ℂ) + 3) / 2)) := by
  apply realGL_continuous_of_contDiffOn
  apply binary_normalizingFactor_contDiffOn (fun matrix => matrix) _ (fun _ member => member)
  intro row column
  fun_prop

theorem functional_binaryCoefficient_continuous (P : Binary.HomogeneousPoly (n + 1))
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Continuous (fun A : BinaryRealGL => functional (binaryCoefficient n A P)) := by
  apply realGL_continuous_of_contDiffOn
  apply binaryCoefficient_functional_contDiffOn (fun matrix => matrix) _
    (fun _ member => member) P functional
  intro row column
  fun_prop

/-- **The scalar tests of the translates of a bounded function are bounded on compact sets**,
uniformly in the adelic point. -/
theorem binaryAmbientRepresentation_bounded
    {κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (bounded : ∀ functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
      ∃ C : ℝ, ∀ h, ‖functional (κ h)‖ ≤ C)
    (K : Set BinaryRealGL) (compact : IsCompact K)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, ∀ A ∈ K, ∀ h, ‖functional (binaryAmbientRepresentation n A κ h)‖ ≤ C := by
  obtain ⟨M, hM⟩ := compact.exists_bound_of_continuousOn
    (normPower_det_atInfinity_continuous (n := n)).continuousOn
  choose D hD using fun position : Fin (n + 2) => compact.exists_bound_of_continuousOn
    (functional_binaryCoefficient_continuous (binaryWeightBasis (n + 1) position)
      functional).continuousOn
  choose C hC using fun position : Fin (n + 2) =>
    bounded ((binaryWeightBasis (n + 1)).coord position)
  refine ⟨M * ∑ position, C position * D position, fun A member h => ?_⟩
  rw [functional_binaryAmbientRepresentation, norm_mul]
  refine mul_le_mul (hM A member) ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun position _ => ?_)) (norm_nonneg _) ((norm_nonneg _).trans
      (hM A member))
  rw [norm_mul]
  exact mul_le_mul (hC position _) (hD position A member) (norm_nonneg _)
    ((norm_nonneg _).trans (hC position h))

/-! ### Regularity -/

/-- **Regularity of a binary family that is a regular binary family plus the coboundary of a
bounded function with continuous translates.** -/
theorem binaryValuesRegular_of_add_coboundary
    {N N₀ : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    {κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)} (regular : BinaryValuesRegular N₀)
    (bounded : ∀ functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
      ∃ C : ℝ, ∀ h, ‖functional (κ h)‖ ≤ C)
    (continuous : ∀ (h : BinaryAdelicGL) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ),
      Continuous (fun A => functional (binaryAmbientRepresentation n A κ h)))
    (decomposition : ∀ A h, N A h = N₀ A h + (binaryAmbientRepresentation n A κ h - κ h)) :
    BinaryValuesRegular N where
  continuous h functional := by
    simp only [decomposition, map_add, map_sub]
    exact (regular.continuous h functional).add ((continuous h functional).sub continuous_const)
  bounded K compact functional := by
    obtain ⟨C₁, h₁⟩ := regular.bounded K compact functional
    obtain ⟨C₂, h₂⟩ := binaryAmbientRepresentation_bounded bounded K compact functional
    obtain ⟨C₃, h₃⟩ := bounded functional
    refine ⟨C₁ + (C₂ + C₃), fun A member h => ?_⟩
    rw [decomposition, map_add, map_sub]
    exact (norm_add_le _ _).trans (add_le_add (h₁ A member h)
      ((norm_sub_le _ _).trans (add_le_add (h₂ A member h) (h₃ h))))

/-- The pointwise Eichler normal form of the scalar weighted realization of a smooth vector is a
regular binary family. -/
theorem binaryValuesRegular_eichlerNormal (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) :
    BinaryValuesRegular (n := n) (eichlerNormal n (endpointScalar cusp halfWeight vector)) where
  continuous := eichlerNormal_continuous _ (endpointScalar_continuousOn cusp halfWeight vector)
  bounded K compact functional := eichlerNormal_bounded _ halfWeight
    (endpointScalar_bound cusp halfWeight vector) K compact functional

/-- **Regularity of the pointwise Eichler normal form plus the coboundary of the lift of a smooth
tuple.** -/
theorem binaryValuesRegular_of_decomposition (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (correction : Fin (n + 2) → cusp.H)
    (correction_smooth : ∀ position, correction position ∈ cusp.smooth)
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (decomposition : ∀ A h, N A h = eichlerNormal n (endpointScalar cusp halfWeight vector) A h +
      (binaryAmbientRepresentation n A (hilbertLift cusp n correction) h -
        hilbertLift cusp n correction h)) :
    BinaryValuesRegular N :=
  binaryValuesRegular_of_add_coboundary (binaryValuesRegular_eichlerNormal cusp halfWeight vector)
    (hilbertLift_bounded cusp correction correction_smooth)
    (hilbertLift_ambient_continuous cusp correction correction_smooth) decomposition

/-- **Regularity of the binary values of the canonical relative cocycle**, given their
decomposition as the pointwise Eichler normal form of a smooth endpoint plus the coboundary of
the lift of a smooth tuple. -/
theorem canonicalBinaryValues_regular (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative) (halfWeight : ℤ)
    (vector : data.cusp.smooth) (correction : Fin (n + 2) → data.cusp.H)
    (correction_smooth : ∀ position, correction position ∈ data.cusp.smooth)
    (decomposition : ∀ A h, canonicalBinaryValues data trivial basis relative regular A h =
      eichlerNormal n (endpointScalar data.cusp halfWeight vector) A h +
        (binaryAmbientRepresentation n A (hilbertLift data.cusp n correction) h -
          hilbertLift data.cusp n correction h)) :
    BinaryValuesRegular (canonicalBinaryValues data trivial basis relative regular) :=
  binaryValuesRegular_of_decomposition data.cusp halfWeight vector correction correction_smooth
    decomposition

end TernaryPeriodPolynomials.AnalyticClasses
