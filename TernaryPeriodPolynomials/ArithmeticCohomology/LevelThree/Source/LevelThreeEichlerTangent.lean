module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerMain

@[expose] public section


/-!
# The level-three Eichler cocycle (untwisted): equivariance of the differential

Plan of the level-three version of the O(2)-normalized Eichler Levi cocycle
(`SourceConstruction.Eichler{Tangent,Equivariance,Primitive,Lift,Regular,Cocycle}`), which
builds the datum `LeviCocycleData` from the spherical holomorphic weight vector.  Here the
datum is `LevelLeviCocycleData` (`GoodPlaneSourceData`), whose smooth lifts only lie in
`levelThreeValues`.

Where SC's chain uses sphericity (`SphericalCusp σ`, `D.vector_spherical`, `cuspSphericalValues`,
`BinaryLevel.finiteCongruence` fixedness via `D.spherical`):

* `EichlerTangent`: `eichler_rho_mul`, `eichler_rho_one`, `eichler_rho_J_J`, `eichler_rho_scalar`,
  `eichler_rho_rotation_J`, hence `eichlerTangent_reflection`, `eichlerTangent_rotation`,
  `eichlerTangent_stabilizer`.  Level-three replacements: SC's `l3_rho_*`
  (`L3EichlerRho`, from `MultiplicityOne.binaryHilbertOperator_mul`,
  `cuspUnitary_positive_scalar`); this file: `lte_tangent_reflection`, `lte_tangent_rotation`,
  `lte_tangent_stabilizer`.
* `EichlerEquivariance`: `eichlerDifferential_equivariant`; here `lte_differential_equivariant`.
  The geometric and sphericity-free lemmas (`eichlerTangent`, `eichlerTangent_real_smul`,
  `eichlerDifferential_formula`, `smulFDeriv_*`) are reused from SC.
* `SphericalDetection.binaryEndpointDifferential_holomorphicForm` (uses `SphericalCusp` through
  the reflection of the affine orbit): here `lte_endpointDifferential_holomorphicForm`, via SC's
  `l3_affineOrbit_reflection`.
* `EichlerPrimitive`, `EichlerLift`, `EichlerRegular`: the potential, the Hilbert-level cocycle, its
  smoothness, finite-level fixedness and the lifts are redone in `LevelThreeEichlerPrimitive` and
  `LevelThreeEichlerLift` on SC's sphericity-free `L3Input` (a holomorphic weight `-(n+3)` vector
  in `levelThreeValues`), with the `+` sign of the untwisted potential `½ (Per z + J Per(-conj z))`;
  `L3Input.form_differentiableOn`, `period_hasDerivAt`, `period_I`, `form_mem_level`,
  `period_fixed`, `fixedLevel` and `lower_rotation` are reused from SC's `L3Eichler*` (they do not
  depend on the sign).  `MultiplicityOne.cuspScalarWeightedRealization_holomorphic`
  replaces `cuspScalarWeightedRealization_holomorphic … D.vector_spherical`.
* `LevelThreeEichlerMain`: the headline `exists_levelLeviCocycleData` and the definition
  `levelThreeEichlerData σ n v hv`, linear in `v`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThreeSource

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.MultiplicityOne (LevelThreeCusp)

section Tangent

variable (σ : CuspidalRepresentation) (n : ℕ)

theorem lte_tangent_reflection (hσ : LevelThreeCusp σ) (e : Fin (n + 2) → σ.H) (d : ℂ) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J (eichlerTangent σ n e d) =
      eichlerTangent σ n e (-(starRingEnd ℂ d)) := by
  unfold eichlerTangent
  simp only [map_smul, map_sub, l3_rho_J_J σ n hσ, map_neg, Complex.conj_conj]
  module

theorem lte_tangent_rotation (hσ : LevelThreeCusp σ) (e : Fin (n + 2) → σ.H)
    (hrot : ∀ θ : Circle,
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) e =
        ((θ : ℂ) ^ 2)⁻¹ • e) (θ : Circle) (d : ℂ) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ)
        (eichlerTangent σ n e d) =
      eichlerTangent σ n e (((θ : ℂ) ^ 2)⁻¹ * d) := by
  have hJ := l3_rho_rotation_J σ n hσ e hrot θ
  have hc : starRingEnd ℂ (((θ : ℂ) ^ 2)⁻¹ * d) = (θ : ℂ) ^ 2 * starRingEnd ℂ d := by
    rw [map_mul, map_inv₀, map_pow, circle_conj_eq_inv, inv_pow, inv_inv]
  unfold eichlerTangent
  simp only [map_smul, map_sub, hrot θ, hJ, hc]
  module

/-- **Equivariance of the tangent vector under the stabilizer of `i`** (level-three version). -/
theorem lte_tangent_stabilizer (hσ : LevelThreeCusp σ)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (e : Fin (n + 2) → σ.H)
    (hrot : ∀ θ : Circle,
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) e =
        ((θ : ℂ) ^ 2)⁻¹ • e)
    (B : BinaryRealGL) (hB : B • UpperHalfPlane.I = UpperHalfPlane.I) (d : ℂ) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) B (eichlerTangent σ n e d) =
      eichlerTangent σ n e (UpperHalfPlane.smulFDeriv B Complex.I d) := by
  have positive_case : ∀ C : BinaryRealGL, 0 < (GeneralLinearGroup.det C).val →
      C • UpperHalfPlane.I = UpperHalfPlane.I → ∀ d : ℂ,
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) C (eichlerTangent σ n e d) =
        eichlerTangent σ n e (UpperHalfPlane.smulFDeriv C Complex.I d) := by
    intro C hpos hC d
    obtain ⟨u, θ, hu, rfl⟩ := binary_stabilizer_positive_decomposition C hpos hC
    rw [smulFDeriv_mul_of_smul_I _ _ (binaryRotations_smul_I θ), ContinuousLinearMap.comp_apply,
      smulFDeriv_scalar_base, ContinuousLinearMap.id_apply, binaryRotations_smulFDeriv,
      l3_rho_mul σ n hσ, lte_tangent_rotation σ n hσ e hrot θ d]
    exact l3_rho_scalar σ n hσ central_positive u hu _
  rcases lt_or_gt_of_ne (GeneralLinearGroup.det B).ne_zero with negative | positive
  · obtain ⟨C, hC_def⟩ : ∃ C : BinaryRealGL, C = B * UpperHalfPlane.J := ⟨_, rfl⟩
    have det_pos : 0 < (GeneralLinearGroup.det C).val := by
      simpa only [hC_def, map_mul, Units.val_mul, UpperHalfPlane.det_J, Units.val_neg,
        Units.val_one, mul_neg_one, neg_pos] using negative
    have fix : C • UpperHalfPlane.I = UpperHalfPlane.I := by
      rw [hC_def, mul_smul, binaryReflection_smul_I, hB]
    have hBC : B = C * UpperHalfPlane.J := by
      rw [hC_def, mul_assoc, eichler_J_mul_J, mul_one]
    rw [hBC, l3_rho_mul σ n hσ, lte_tangent_reflection σ n hσ,
      positive_case C det_pos fix, smulFDeriv_mul_of_smul_I C UpperHalfPlane.J
        binaryReflection_smul_I,
      ContinuousLinearMap.comp_apply, binaryReflection_smulFDeriv]
  · exact positive_case B positive hB d

end Tangent

section Orbit

/-- Both complex types of the full plane differential, with all height powers canceled
(level-three version of `binaryEndpointDifferential_holomorphicForm`). -/
theorem lte_endpointDifferential_holomorphicForm (σ : CuspidalRepresentation)
    (hσ : LevelThreeCusp σ) (degree : ℕ) (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (vector : σ.H) (point : ℂ) (positive : 0 < point.im) (direction : ℂ) :
    binaryEndpointDifferential σ (binaryWeightBasis (degree + 1)) (Pi.single 0 vector) point
        direction =
      (2 : ℂ)⁻¹ • (direction • binaryEndpointHolomorphicForm σ degree halfWeight vector point -
        (starRingEnd ℂ direction) • binaryHilbertOperator σ (binaryWeightBasis (degree + 1))
          UpperHalfPlane.J
          (binaryEndpointHolomorphicForm σ degree halfWeight vector
            (binaryComplexReflection point))) := by
  have reflected_positive : 0 < (binaryComplexReflection point).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have reflected_weighted : point.im⁻¹ •
      binaryAffineOrbitVector σ (binaryWeightBasis (degree + 1))
        (binaryHilbertOperator σ (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
          (Pi.single 0 vector)) point =
      binaryHilbertOperator σ (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
        (binaryEndpointHolomorphicForm σ degree halfWeight vector
          (binaryComplexReflection point)) := by
    rw [l3_affineOrbit_reflection σ hσ _ _ point positive,
      ← ContinuousLinearMap.map_smul_of_tower]
    congr 1
    rw [← binaryComplexReflection_im point]
    exact binaryEndpointHolomorphicForm_eq σ degree halfWeight weight vector _ reflected_positive
  change point.im⁻¹ • binaryHilbertOperator σ (binaryWeightBasis (degree + 1))
    (invertibleMatrix (binaryUpperSectionMatrix point))
    ((2 : ℂ)⁻¹ • (direction • (Pi.single 0 vector : Fin (degree + 2) → σ.H) -
      (starRingEnd ℂ direction) •
        binaryHilbertOperator σ (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
          (Pi.single 0 vector))) = _
  rw [map_smul, map_sub, map_smul, map_smul, smul_comm point.im⁻¹, smul_sub,
    smul_comm point.im⁻¹ direction, smul_comm point.im⁻¹ (starRingEnd ℂ direction)]
  change (2 : ℂ)⁻¹ • (direction •
    (point.im⁻¹ • binaryAffineOrbitVector σ (binaryWeightBasis (degree + 1))
      (Pi.single 0 vector) point) -
      (starRingEnd ℂ direction) • (point.im⁻¹ • binaryAffineOrbitVector σ
        (binaryWeightBasis (degree + 1))
        (binaryHilbertOperator σ (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
          (Pi.single 0 vector)) point)) = _
  rw [binaryEndpointHolomorphicForm_eq σ degree halfWeight weight vector point positive,
    reflected_weighted]

end Orbit

section Equivariance

variable (σ : CuspidalRepresentation) (n : ℕ)

/-- **Equivariance of the Eichler differential** (level-three version). -/
theorem lte_differential_equivariant (hσ : LevelThreeCusp σ)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (e : Fin (n + 2) → σ.H)
    (hrot : ∀ θ : Circle,
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) e =
        ((θ : ℂ) ^ 2)⁻¹ • e)
    (A : BinaryRealGL) (p : UpperHalfPlane) (d : ℂ) :
    binaryEndpointDifferential σ (binaryWeightBasis (n + 1)) e ((A • p : UpperHalfPlane) : ℂ)
        (UpperHalfPlane.smulFDeriv A (p : ℂ) d) =
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A
        (binaryEndpointDifferential σ (binaryWeightBasis (n + 1)) e (p : ℂ) d) := by
  obtain ⟨S, hS⟩ : ∃ S : BinaryRealGL, S = binarySymmetricSection p := ⟨_, rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S : BinaryRealGL, S = binarySymmetricSection (A • p) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : BinaryRealGL, B = S'⁻¹ * A * S := ⟨_, rfl⟩
  have hSI : S • UpperHalfPlane.I = p := by rw [hS]; exact binarySymmetricSection_smul p
  have hS'I : S' • UpperHalfPlane.I = A • p := by rw [hS']; exact binarySymmetricSection_smul _
  have AS : A * S = S' * B := by rw [hB]; group
  have hBI : B • UpperHalfPlane.I = UpperHalfPlane.I := by
    have h1 : (S' * B) • UpperHalfPlane.I = A • p := by rw [← AS, mul_smul, hSI]
    rw [mul_smul, ← hS'I] at h1
    exact smul_left_cancel S' h1
  have key : (UpperHalfPlane.smulFDeriv A (p : ℂ)).comp (UpperHalfPlane.smulFDeriv S Complex.I) =
      (UpperHalfPlane.smulFDeriv S' Complex.I).comp (UpperHalfPlane.smulFDeriv B Complex.I) := by
    have c1 := smulFDeriv_mul_base A S UpperHalfPlane.I
    have c2 := smulFDeriv_mul_of_smul_I S' B hBI
    rw [hSI, UpperHalfPlane.coe_I] at c1
    rw [← c1, ← c2, AS]
  have hp : p.im ≠ 0 := p.im_pos.ne'
  have hy : (A • p).im ≠ 0 := (A • p).im_pos.ne'
  have sd : UpperHalfPlane.smulFDeriv S Complex.I ((p.im)⁻¹ • d) = d := by
    rw [hS, binarySymmetricSection_smulFDeriv, smul_smul, mul_inv_cancel₀ hp, one_smul]
  have hd : UpperHalfPlane.smulFDeriv A (p : ℂ) d =
      (A • p).im • (p.im)⁻¹ • UpperHalfPlane.smulFDeriv B Complex.I d := by
    have applied := congrArg (fun L => L ((p.im)⁻¹ • d)) key
    simp only [ContinuousLinearMap.comp_apply, sd] at applied
    rw [applied, hS', binarySymmetricSection_smulFDeriv, map_smul]
  have K := lte_tangent_stabilizer σ n hσ central_positive e hrot B hBI d
  have right : binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A
      (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S (eichlerTangent σ n e d)) =
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S'
        (eichlerTangent σ n e (UpperHalfPlane.smulFDeriv B Complex.I d)) := by
    rw [← l3_rho_mul σ n hσ, AS, l3_rho_mul σ n hσ, K]
  have cancel : ((((A • p).im)⁻¹ : ℝ) : ℂ) * (((A • p).im : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hy, Complex.ofReal_one]
  have rhs : binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A
      ((p.im)⁻¹ • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S
        (eichlerTangent σ n e d)) =
      ((((p.im)⁻¹ : ℝ) : ℂ)) • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S'
        (eichlerTangent σ n e (UpperHalfPlane.smulFDeriv B Complex.I d)) := by
    rw [real_smul_eq_coe (p.im)⁻¹
      (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S (eichlerTangent σ n e d)),
      map_smul, right]
  have lhs : ((A • p).im)⁻¹ • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S'
      (eichlerTangent σ n e ((A • p).im • (p.im)⁻¹ • UpperHalfPlane.smulFDeriv B Complex.I d)) =
      ((((p.im)⁻¹ : ℝ) : ℂ)) • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S'
        (eichlerTangent σ n e (UpperHalfPlane.smulFDeriv B Complex.I d)) := by
    rw [eichlerTangent_real_smul, eichlerTangent_real_smul, map_smul, map_smul,
      real_smul_eq_coe ((A • p).im)⁻¹]
    simp only [smul_smul]
    congr 1
    rw [← mul_assoc, cancel, one_mul]
  rw [eichlerDifferential_formula σ n e (A • p), eichlerDifferential_formula σ n e p, ← hS', ← hS,
    hd]
  exact lhs.trans rhs.symm

end Equivariance

end TernaryPeriodPolynomials.LevelThreeSource

end
