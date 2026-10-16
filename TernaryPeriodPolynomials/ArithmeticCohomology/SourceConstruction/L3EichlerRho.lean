module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Equivariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.EichlerTwTangent
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgeMain

@[expose] public section


/-!
# Level-three version of the sign-twisted equivariance of the Eichler differential

The sign-twisted tangent chain of `AxiomCodeTwistedSource/EichlerTwTangent` uses the hypothesis
`SphericalCusp σ` only through the multiplicativity of the Hilbert binary operators, their
triviality on positive scalars and the reflection compatibility of the affine orbit.  All three are
available for a cuspidal representation with a nonzero level-three vector
(`MultiplicityOne.binaryHilbertOperator_mul`, `…cuspUnitary_positive_scalar`).  This file
reproves the chain with `LevelThreeCusp σ` in place of `SphericalCusp σ`, with the proofs of the
original declarations.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.MultiplicityOne (LevelThreeCusp)

section Rho

variable (σ : CuspidalRepresentation) (n : ℕ)

theorem l3_rho_mul (hσ : LevelThreeCusp σ) (A B : BinaryRealGL) (x : Fin (n + 2) → σ.H) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (A * B) x =
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A
        (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) B x) := by
  rw [MultiplicityOne.binaryHilbertOperator_mul σ hσ (binaryWeightBasis (n + 1)) A B]
  rfl

theorem l3_rho_one (hσ : LevelThreeCusp σ) (x : Fin (n + 2) → σ.H) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) 1 x = x := by
  rw [MultiplicityOne.binaryHilbertOperator_one σ hσ (binaryWeightBasis (n + 1))]
  rfl

theorem l3_rho_J_J (hσ : LevelThreeCusp σ) (x : Fin (n + 2) → σ.H) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
      (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J x) = x := by
  rw [← l3_rho_mul σ n hσ, eichler_J_mul_J, l3_rho_one σ n hσ]

/-- A positive real scalar acts trivially on tuples of a representation whose central character
is trivial on the positive reals. -/
theorem l3_rho_scalar (hσ : LevelThreeCusp σ)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (u : ℝˣ) (hu : 0 < u.val) (x : Fin (n + 2) → σ.H) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (GeneralLinearGroup.scalar (Fin 2) u) x =
      x := by
  funext position
  have u_ne : (u.val : ℂ) ≠ 0 := by exact_mod_cast u.ne_zero
  rw [binaryHilbertOperator_apply, binary_scalar_normalizingFactor n u hu]
  rw [Finset.sum_eq_single position]
  · rw [binaryCoefficient_scalar, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, ite_eq_left rfl, smul_eq_mul, mul_one,
      MultiplicityOne.cuspUnitary_positive_scalar σ hσ central_positive u hu, smul_smul,
      ← mul_pow, mul_inv_cancel₀ u_ne, one_pow, one_smul]
  · intro source _ different
    rw [binaryCoefficient_scalar, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, ite_eq_right different, smul_zero, zero_smul]
  · intro absent
    exact absurd (Finset.mem_univ _) absent

theorem l3_rho_rotation_J (hσ : LevelThreeCusp σ) (e : Fin (n + 2) → σ.H)
    (hrot : ∀ θ : Circle, binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) e =
      ((θ : ℂ) ^ 2)⁻¹ • e) (θ : Circle) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ)
        (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J e) =
      (θ : ℂ) ^ 2 • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J e := by
  have comm : binaryRotations θ * UpperHalfPlane.J = UpperHalfPlane.J * binaryRotations θ⁻¹ := by
    have := eichler_J_mul_rotation θ⁻¹
    rw [inv_inv] at this
    exact this.symm
  rw [← l3_rho_mul σ n hσ, comm, l3_rho_mul σ n hσ, hrot θ⁻¹, map_smul,
    circle_coe_inv, inv_pow, inv_inv]

end Rho

section Tangent

variable (σ : CuspidalRepresentation) (n : ℕ)

theorem l3_eichlerTangentTw_reflection (hσ : LevelThreeCusp σ) (e : Fin (n + 2) → σ.H)
    (d : ℂ) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
        (eichlerTangentTw σ n e d) =
      -eichlerTangentTw σ n e (-(starRingEnd ℂ d)) := by
  unfold eichlerTangentTw
  simp only [map_smul, map_add, l3_rho_J_J σ n hσ, map_neg, Complex.conj_conj]
  module

theorem l3_eichlerTangentTw_rotation (hσ : LevelThreeCusp σ) (e : Fin (n + 2) → σ.H)
    (hrot : ∀ θ : Circle,
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) e =
        ((θ : ℂ) ^ 2)⁻¹ • e) (θ : Circle) (d : ℂ) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ)
        (eichlerTangentTw σ n e d) =
      eichlerTangentTw σ n e (((θ : ℂ) ^ 2)⁻¹ * d) := by
  have hJ := l3_rho_rotation_J σ n hσ e hrot θ
  have hc : starRingEnd ℂ (((θ : ℂ) ^ 2)⁻¹ * d) = (θ : ℂ) ^ 2 * starRingEnd ℂ d := by
    rw [map_mul, map_inv₀, map_pow, circle_conj_eq_inv, inv_pow, inv_inv]
  unfold eichlerTangentTw
  simp only [map_smul, map_add, hrot θ, hJ, hc]
  module

/-- **Sign-twisted equivariance of the tangent vector under the stabilizer of `i`.** -/
theorem l3_eichlerTangentTw_stabilizer (hσ : LevelThreeCusp σ)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (e : Fin (n + 2) → σ.H)
    (hrot : ∀ θ : Circle,
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) e =
        ((θ : ℂ) ^ 2)⁻¹ • e)
    (B : BinaryRealGL) (hB : B • UpperHalfPlane.I = UpperHalfPlane.I) (d : ℂ) :
    signDet B • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) B
        (eichlerTangentTw σ n e d) =
      eichlerTangentTw σ n e (UpperHalfPlane.smulFDeriv B Complex.I d) := by
  have positive_case : ∀ C : BinaryRealGL, 0 < (GeneralLinearGroup.det C).val →
      C • UpperHalfPlane.I = UpperHalfPlane.I → ∀ d : ℂ,
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) C (eichlerTangentTw σ n e d) =
        eichlerTangentTw σ n e (UpperHalfPlane.smulFDeriv C Complex.I d) := by
    intro C hpos hC d
    obtain ⟨u, θ, hu, rfl⟩ := binary_stabilizer_positive_decomposition C hpos hC
    rw [smulFDeriv_mul_of_smul_I _ _ (binaryRotations_smul_I θ), ContinuousLinearMap.comp_apply,
      smulFDeriv_scalar_base, ContinuousLinearMap.id_apply, binaryRotations_smulFDeriv,
      l3_rho_mul σ n hσ, l3_eichlerTangentTw_rotation σ n hσ e hrot θ d]
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
    rw [hBC, signDet_mul, signDet_of_pos det_pos, signDet_J, l3_rho_mul σ n hσ,
      l3_eichlerTangentTw_reflection σ n hσ, map_neg, positive_case C det_pos fix,
      smulFDeriv_mul_of_smul_I C UpperHalfPlane.J binaryReflection_smul_I,
      ContinuousLinearMap.comp_apply, binaryReflection_smulFDeriv, one_mul, neg_smul, one_smul,
      neg_neg]
  · rw [signDet_of_pos positive, one_smul]
    exact positive_case B positive hB d

end Tangent

section Orbit

theorem l3_affineOrbit_reflection {degree : ℕ} {index : Type} [Fintype index]
    (cusp : CuspidalRepresentation) (hσ : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (vector : index → cusp.H) (point : ℂ) (positive : 0 < point.im) :
    binaryAffineOrbitVector cusp basis (binaryHilbertOperator cusp basis UpperHalfPlane.J vector)
        point =
      binaryHilbertOperator cusp basis UpperHalfPlane.J
        (binaryAffineOrbitVector cusp basis vector (binaryComplexReflection point)) := by
  let upper : UpperHalfPlane := ⟨point, positive⟩
  let reflected : UpperHalfPlane :=
    ⟨binaryComplexReflection point, by rw [binaryComplexReflection_im]; exact positive⟩
  rw [binaryAffineOrbitVector, binaryUpperSectionMatrix_coe upper, invertibleMatrix_coe,
    binaryAffineOrbitVector, binaryUpperSectionMatrix_coe reflected, invertibleMatrix_coe]
  change ((binaryHilbertOperator cusp basis (binarySymmetricSection upper)).comp
      (binaryHilbertOperator cusp basis UpperHalfPlane.J)) vector =
    ((binaryHilbertOperator cusp basis UpperHalfPlane.J).comp
      (binaryHilbertOperator cusp basis (binarySymmetricSection reflected))) vector
  rw [← MultiplicityOne.binaryHilbertOperator_mul cusp hσ,
    ← MultiplicityOne.binaryHilbertOperator_mul cusp hσ,
    binarySymmetricSection_mul_reflection]

/-- Both complex types of the sign-twisted plane differential, with all height powers canceled. -/
theorem l3_endpointDifferentialTw_holomorphicForm (σ : CuspidalRepresentation)
    (hσ : LevelThreeCusp σ) (degree : ℕ) (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (vector : σ.H) (point : ℂ) (positive : 0 < point.im) (direction : ℂ) :
    binaryEndpointDifferentialTw σ (binaryWeightBasis (degree + 1)) (Pi.single 0 vector) point
        direction =
      (2 : ℂ)⁻¹ • (direction • binaryEndpointHolomorphicForm σ degree halfWeight vector point +
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
    ((2 : ℂ)⁻¹ • (direction • (Pi.single 0 vector : Fin (degree + 2) → σ.H) +
      (starRingEnd ℂ direction) •
        binaryHilbertOperator σ (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
          (Pi.single 0 vector))) = _
  rw [map_smul, map_add, map_smul, map_smul, smul_comm point.im⁻¹, smul_add,
    smul_comm point.im⁻¹ direction, smul_comm point.im⁻¹ (starRingEnd ℂ direction)]
  change (2 : ℂ)⁻¹ • (direction •
    (point.im⁻¹ • binaryAffineOrbitVector σ (binaryWeightBasis (degree + 1))
      (Pi.single 0 vector) point) +
      (starRingEnd ℂ direction) • (point.im⁻¹ • binaryAffineOrbitVector σ
        (binaryWeightBasis (degree + 1))
        (binaryHilbertOperator σ (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
          (Pi.single 0 vector)) point)) = _
  rw [binaryEndpointHolomorphicForm_eq σ degree halfWeight weight vector point positive,
    reflected_weighted]

end Orbit

section Equivariance

variable (σ : CuspidalRepresentation) (n : ℕ)

/-- **Sign-twisted equivariance of the Eichler differential** (level-three version). -/
theorem l3_eichlerDifferentialTw_equivariant (hσ : LevelThreeCusp σ)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (e : Fin (n + 2) → σ.H)
    (hrot : ∀ θ : Circle,
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) e =
        ((θ : ℂ) ^ 2)⁻¹ • e)
    (A : BinaryRealGL) (p : UpperHalfPlane) (d : ℂ) :
    binaryEndpointDifferentialTw σ (binaryWeightBasis (n + 1)) e ((A • p : UpperHalfPlane) : ℂ)
        (UpperHalfPlane.smulFDeriv A (p : ℂ) d) =
      signDet A • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A
        (binaryEndpointDifferentialTw σ (binaryWeightBasis (n + 1)) e (p : ℂ) d) := by
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
  have hS1 : signDet S = 1 :=
    signDet_of_pos (by rw [hS, binarySymmetricSection_det]; norm_num)
  have hS'1 : signDet S' = 1 :=
    signDet_of_pos (by rw [hS', binarySymmetricSection_det]; norm_num)
  have hsign : signDet A = signDet B := by
    have product := congrArg signDet AS
    rwa [signDet_mul, signDet_mul, hS1, hS'1, mul_one, one_mul] at product
  have K := l3_eichlerTangentTw_stabilizer σ n hσ central_positive e hrot B hBI d
  have right : signDet A • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A
      (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S (eichlerTangentTw σ n e d)) =
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S'
        (eichlerTangentTw σ n e (UpperHalfPlane.smulFDeriv B Complex.I d)) := by
    have pull := map_smul (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S') (signDet B)
      (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) B (eichlerTangentTw σ n e d))
    rw [← l3_rho_mul σ n hσ, AS, l3_rho_mul σ n hσ, hsign, ← pull, K]
  have cancel : ((((A • p).im)⁻¹ : ℝ) : ℂ) * (((A • p).im : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hy, Complex.ofReal_one]
  have rhs : signDet A • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A
      ((p.im)⁻¹ • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S
        (eichlerTangentTw σ n e d)) =
      ((((p.im)⁻¹ : ℝ) : ℂ)) • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S'
        (eichlerTangentTw σ n e (UpperHalfPlane.smulFDeriv B Complex.I d)) := by
    rw [real_smul_eq_coe (p.im)⁻¹
      (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S (eichlerTangentTw σ n e d)),
      map_smul, smul_comm (signDet A) ((((p.im)⁻¹ : ℝ) : ℂ)), right]
  have lhs : ((A • p).im)⁻¹ • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S'
      (eichlerTangentTw σ n e ((A • p).im • (p.im)⁻¹ • UpperHalfPlane.smulFDeriv B Complex.I d)) =
      ((((p.im)⁻¹ : ℝ) : ℂ)) • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S'
        (eichlerTangentTw σ n e (UpperHalfPlane.smulFDeriv B Complex.I d)) := by
    rw [eichlerTangentTw_real_smul, eichlerTangentTw_real_smul, map_smul, map_smul,
      real_smul_eq_coe ((A • p).im)⁻¹]
    simp only [smul_smul]
    congr 1
    rw [← mul_assoc, cancel, one_mul]
  rw [eichlerDifferentialTw_formula σ n e (A • p), eichlerDifferentialTw_formula σ n e p,
    ← hS', ← hS, hd]
  exact lhs.trans rhs.symm

end Equivariance

end TernaryPeriodPolynomials.SourceConstruction

end
