module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Equivariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.IwasawaPhase
public import Mathlib.Tactic.Module

@[expose] public section


/-!
# The sign-twisted tangent vector of the Eichler differential

For the odd quadratic character the Levi `GL₂(ℝ)` acts through the sign-twisted representation
`ρ'(A) = sign(det A) ρ(A)`.  The cocycle needed there is built from the antisymmetrised potential
`P⁻(z) = ½ (Per z - J Per(-z̄))`, whose real differential has the tangent vector
`T⁻ e d = ½ (d e + conj d · J e)`.  This file proves the algebraic core of its equivariance:
`ρ'(B) (T⁻ e d) = T⁻ e (Dρ_B(i) d)` for every `B` fixing `i`, and the resulting equivariance
`η⁻_{A z}(D A_z d) = ρ'(A) η⁻_z(d)` of the twisted endpoint differential.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.TwistedSource

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
  (eichler_rho_mul eichler_rho_J_J eichler_J_mul_J real_smul_eq_coe eichler_rho_scalar
    eichler_rho_rotation_J circle_conj_eq_inv smulFDeriv_mul_base smulFDeriv_mul_of_smul_I
    smulFDeriv_scalar_base)

section SignDet

/-- The sign of the real determinant, as a complex number. -/
def signDet (A : BinaryRealGL) : ℂ := if 0 < (GeneralLinearGroup.det A).val then 1 else -1

theorem sign_ite_mul (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (if 0 < x * y then (1 : ℂ) else -1) =
      (if 0 < x then (1 : ℂ) else -1) * (if 0 < y then (1 : ℂ) else -1) := by
  rcases lt_or_gt_of_ne hx with a | a <;> rcases lt_or_gt_of_ne hy with b | b
  · rw [ite_eq_left (mul_pos_of_neg_of_neg a b), ite_eq_right (not_lt.2 a.le), ite_eq_right (not_lt.2 b.le)]
    norm_num
  · rw [ite_eq_right (not_lt.2 (mul_neg_of_neg_of_pos a b).le), ite_eq_right (not_lt.2 a.le), ite_eq_left b]
    norm_num
  · rw [ite_eq_right (not_lt.2 (mul_neg_of_pos_of_neg a b).le), ite_eq_left a, ite_eq_right (not_lt.2 b.le)]
    norm_num
  · rw [ite_eq_left (mul_pos a b), ite_eq_left a, ite_eq_left b]
    norm_num

theorem signDet_mul (A B : BinaryRealGL) : signDet (A * B) = signDet A * signDet B := by
  unfold signDet
  rw [map_mul, Units.val_mul]
  exact sign_ite_mul _ _ (GeneralLinearGroup.det A).ne_zero (GeneralLinearGroup.det B).ne_zero

theorem signDet_one : signDet (1 : BinaryRealGL) = 1 := by
  simp [signDet]

theorem signDet_J : signDet UpperHalfPlane.J = -1 := by
  have h : (GeneralLinearGroup.det UpperHalfPlane.J).val = -1 := by
    rw [UpperHalfPlane.det_J, Units.val_neg, Units.val_one]
  unfold signDet
  rw [h]
  norm_num

theorem signDet_of_pos {A : BinaryRealGL} (h : 0 < (GeneralLinearGroup.det A).val) :
    signDet A = 1 := by
  unfold signDet
  rw [ite_eq_left h]

theorem signDet_sq (A : BinaryRealGL) : signDet A * signDet A = 1 := by
  unfold signDet
  split_ifs <;> norm_num

end SignDet

section Algebra

variable (σ : CuspidalRepresentation) (n : ℕ)

/-- The real-linear tangent vector `½ (d e + conj d · J e)` of the antisymmetrised potential. -/
def eichlerTangentTw (e : Fin (n + 2) → σ.H) (d : ℂ) : Fin (n + 2) → σ.H :=
  (2 : ℂ)⁻¹ • (d • e + (starRingEnd ℂ d) •
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J e)

theorem eichlerTangentTw_reflection (spherical : SphericalCusp σ) (e : Fin (n + 2) → σ.H)
    (d : ℂ) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
        (eichlerTangentTw σ n e d) =
      -eichlerTangentTw σ n e (-(starRingEnd ℂ d)) := by
  unfold eichlerTangentTw
  simp only [map_smul, map_add, eichler_rho_J_J σ n spherical, map_neg, Complex.conj_conj]
  module

theorem eichlerTangentTw_rotation (spherical : SphericalCusp σ) (e : Fin (n + 2) → σ.H)
    (hrot : ∀ θ : Circle,
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) e =
        ((θ : ℂ) ^ 2)⁻¹ • e) (θ : Circle) (d : ℂ) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ)
        (eichlerTangentTw σ n e d) =
      eichlerTangentTw σ n e (((θ : ℂ) ^ 2)⁻¹ * d) := by
  have hJ := eichler_rho_rotation_J σ n spherical e hrot θ
  have hc : starRingEnd ℂ (((θ : ℂ) ^ 2)⁻¹ * d) = (θ : ℂ) ^ 2 * starRingEnd ℂ d := by
    rw [map_mul, map_inv₀, map_pow, circle_conj_eq_inv, inv_pow, inv_inv]
  unfold eichlerTangentTw
  simp only [map_smul, map_add, hrot θ, hJ, hc]
  module

theorem eichlerTangentTw_real_smul (e : Fin (n + 2) → σ.H) (r : ℝ) (d : ℂ) :
    eichlerTangentTw σ n e (r • d) = (r : ℂ) • eichlerTangentTw σ n e d := by
  unfold eichlerTangentTw
  rw [Complex.real_smul, map_mul, Complex.conj_ofReal]
  module

/-- **Sign-twisted equivariance of the tangent vector under the stabilizer of `i`.** -/
theorem eichlerTangentTw_stabilizer (spherical : SphericalCusp σ)
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
      eichler_rho_mul σ n spherical, eichlerTangentTw_rotation σ n spherical e hrot θ d]
    exact eichler_rho_scalar σ n spherical central_positive u hu _
  rcases lt_or_gt_of_ne (GeneralLinearGroup.det B).ne_zero with negative | positive
  · obtain ⟨C, hC_def⟩ : ∃ C : BinaryRealGL, C = B * UpperHalfPlane.J := ⟨_, rfl⟩
    have det_pos : 0 < (GeneralLinearGroup.det C).val := by
      simpa only [hC_def, map_mul, Units.val_mul, UpperHalfPlane.det_J, Units.val_neg,
        Units.val_one, mul_neg_one, neg_pos] using negative
    have fix : C • UpperHalfPlane.I = UpperHalfPlane.I := by
      rw [hC_def, mul_smul, binaryReflection_smul_I, hB]
    have hBC : B = C * UpperHalfPlane.J := by
      rw [hC_def, mul_assoc, eichler_J_mul_J, mul_one]
    rw [hBC, signDet_mul, signDet_of_pos det_pos, signDet_J, eichler_rho_mul σ n spherical,
      eichlerTangentTw_reflection σ n spherical, map_neg, positive_case C det_pos fix,
      smulFDeriv_mul_of_smul_I C UpperHalfPlane.J binaryReflection_smul_I,
      ContinuousLinearMap.comp_apply, binaryReflection_smulFDeriv, one_mul, neg_smul, one_smul,
      neg_neg]
  · rw [signDet_of_pos positive, one_smul]
    exact positive_case B positive hB d

end Algebra

/-- The sign-twisted real differential of the endpoint potential. -/
def binaryEndpointDifferentialTw (σ : CuspidalRepresentation) {degree : ℕ} {index : Type}
    [Fintype index] (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (lower : index → σ.H) (point direction : ℂ) : index → σ.H :=
  point.im⁻¹ • binaryAffineOrbitVector σ basis
    ((2 : ℂ)⁻¹ • (direction • lower + (starRingEnd ℂ direction) •
      binaryHilbertOperator σ basis UpperHalfPlane.J lower)) point

/-- Both complex types of the sign-twisted plane differential, with all height powers canceled. -/
theorem binaryEndpointDifferentialTw_holomorphicForm (σ : CuspidalRepresentation)
    (spherical : SphericalCusp σ) (degree : ℕ) (halfWeight : ℤ)
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
    rw [binaryAffineOrbitVector_reflection σ spherical _ _ point positive,
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

section Equivariance

variable (σ : CuspidalRepresentation) (n : ℕ)

theorem eichlerDifferentialTw_formula (e : Fin (n + 2) → σ.H) (p : UpperHalfPlane) (d : ℂ) :
    binaryEndpointDifferentialTw σ (binaryWeightBasis (n + 1)) e (p : ℂ) d =
      (p.im)⁻¹ • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binarySymmetricSection p)
        (eichlerTangentTw σ n e d) := by
  unfold binaryEndpointDifferentialTw binaryAffineOrbitVector
  rw [binaryUpperSectionMatrix_coe p, invertibleMatrix_coe]
  rfl

/-- **Sign-twisted equivariance of the Eichler differential.** -/
theorem eichlerDifferentialTw_equivariant (spherical : SphericalCusp σ)
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
  have K := eichlerTangentTw_stabilizer σ n spherical central_positive e hrot B hBI d
  have right : signDet A • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A
      (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S (eichlerTangentTw σ n e d)) =
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S'
        (eichlerTangentTw σ n e (UpperHalfPlane.smulFDeriv B Complex.I d)) := by
    have pull := map_smul (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S') (signDet B)
      (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) B (eichlerTangentTw σ n e d))
    rw [← eichler_rho_mul σ n spherical, AS, eichler_rho_mul σ n spherical, hsign, ← pull, K]
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

end TernaryPeriodPolynomials.TwistedSource

end
