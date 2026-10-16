module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Tangent
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeCocycle

@[expose] public section


/-!
# Equivariance of the Eichler differential

The real differential `η_z(d) = (Im z)⁻¹ ρ(s(z)) (T e d)` of the Eichler form of a weight tuple
`e` is `GL₂(ℝ)`-equivariant: `η_{A z}(D A_z d) = ρ(A) η_z(d)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The input of the Eichler construction: a nonzero spherical holomorphic lowest-weight vector. -/
structure EichlerInput (σ : CuspidalRepresentation) (n : ℕ) where
  central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1
  halfWeight : ℤ
  weight : 2 * halfWeight = -((n : ℤ) + 3)
  vector : σ.smooth
  vector_ne : vector ≠ 0
  vector_spherical : vector.val ∈ cuspSphericalValues σ
  rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) vector.val =
    (angle : ℂ) ^ (2 * halfWeight) • vector.val
  holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit σ halfWeight vector.val)
    UpperHalfPlane.upperHalfPlaneSet

namespace EichlerInput

variable {σ : CuspidalRepresentation} {n : ℕ} (D : EichlerInput σ n)

include D in
theorem spherical : SphericalCusp σ :=
  ⟨D.vector, D.vector_ne, fun k => D.vector_spherical k⟩

/-- The lowest-weight tuple. -/
def lower : Fin (n + 2) → σ.H := Pi.single 0 D.vector.val

theorem lower_rotation (θ : Circle) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) D.lower =
      ((θ : ℂ) ^ 2)⁻¹ • D.lower := by
  have hw := D.weight
  have coordinates : ∀ (position : Fin (n + 2)) (angle : Circle),
      σ.π (atInfinity (binaryRotations angle)) (D.lower position) =
        (angle : ℂ) ^ binaryUnitaryWeight n (-2) position • D.lower position := by
    intro position angle
    by_cases h : position = 0
    · subst h
      have weight_eq : binaryUnitaryWeight n (-2) 0 = 2 * D.halfWeight := by
        simp [binaryUnitaryWeight]
        omega
      rw [weight_eq]
      simp only [lower, Pi.single_eq_same]
      exact D.rotation angle
    · simp only [lower, Pi.single_eq_of_ne h, map_zero, smul_zero]
  rw [binaryWeightBasis_eigenvector_of_coordinates σ n (-2) D.lower coordinates θ, _root_.zpow_neg]
  norm_num

end EichlerInput

theorem real_smul_eq_coe {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] (r : ℝ) (x : E) : r • x = (r : ℂ) • x :=
  (IsScalarTower.algebraMap_smul ℂ r x).symm

section Equivariance

variable (σ : CuspidalRepresentation) (n : ℕ)

theorem eichlerTangent_real_smul (e : Fin (n + 2) → σ.H) (r : ℝ) (d : ℂ) :
    eichlerTangent σ n e (r • d) = (r : ℂ) • eichlerTangent σ n e d := by
  unfold eichlerTangent
  rw [Complex.real_smul, map_mul, Complex.conj_ofReal]
  module

theorem eichlerDifferential_formula (e : Fin (n + 2) → σ.H) (p : UpperHalfPlane) (d : ℂ) :
    binaryEndpointDifferential σ (binaryWeightBasis (n + 1)) e (p : ℂ) d =
      (p.im)⁻¹ • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binarySymmetricSection p)
        (eichlerTangent σ n e d) := by
  unfold binaryEndpointDifferential binaryAffineOrbitVector
  rw [binaryUpperSectionMatrix_coe p, invertibleMatrix_coe]
  rfl

/-- **Equivariance of the Eichler differential.** -/
theorem eichlerDifferential_equivariant (spherical : SphericalCusp σ)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (e : Fin (n + 2) → σ.H)
    (hrot : ∀ θ : Circle, binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) e =
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
  have K := eichlerTangent_stabilizer σ n spherical central_positive e hrot B hBI d
  have right : binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A
      (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S (eichlerTangent σ n e d)) =
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S'
        (eichlerTangent σ n e (UpperHalfPlane.smulFDeriv B Complex.I d)) := by
    rw [← eichler_rho_mul σ n spherical, AS, eichler_rho_mul σ n spherical, K]
  have cancel : ((((A • p).im)⁻¹ : ℝ) : ℂ) * (((A • p).im : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hy, Complex.ofReal_one]
  have rhs : binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A
      ((p.im)⁻¹ • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) S (eichlerTangent σ n e d)) =
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

end TernaryPeriodPolynomials.SourceConstruction

end
