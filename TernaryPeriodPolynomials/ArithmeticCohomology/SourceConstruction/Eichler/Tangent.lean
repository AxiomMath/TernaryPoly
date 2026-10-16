module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.BridgeIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeightAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.UnitaryCentral
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CentralAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.TangentCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SymmetricSpace
public import Mathlib.Tactic.Module

@[expose] public section


/-!
# Equivariance of the real tangent vector of an Eichler form

For a weight tuple `e` of the Hilbert representation of `GL₂(ℝ)` on `Sym^{n+1}`-tuples whose
rotation action is `θ ↦ (θ²)⁻¹`, the real-linear tangent vector
`T e d = ½ (d e - conj d · J e)` satisfies `ρ(B) (T e d) = T e (Dρ_B(i) d)` for every `B`
fixing `i`.  This is the algebraic core of the equivariance of the Eichler differential.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

section Circle

theorem circle_conj_eq_inv (θ : Circle) : starRingEnd ℂ (θ : ℂ) = (θ : ℂ)⁻¹ :=
  (Complex.inv_eq_conj (Circle.norm_coe θ)).symm

theorem circle_coe_inv (θ : Circle) : ((θ⁻¹ : Circle) : ℂ) = (θ : ℂ)⁻¹ := by
  rw [Circle.coe_inv_eq_conj, circle_conj_eq_inv]

end Circle

section Geometry

/-- Chain rule for the real derivative of the Möbius action. -/
theorem smulFDeriv_mul_base (g h : BinaryRealGL) (z : UpperHalfPlane) :
    UpperHalfPlane.smulFDeriv (g * h) (z : ℂ) =
      (UpperHalfPlane.smulFDeriv g ((h • z : UpperHalfPlane) : ℂ)).comp
        (UpperHalfPlane.smulFDeriv h (z : ℂ)) := by
  have inner := (UpperHalfPlane.hasStrictFDerivAt_smul h z).hasFDerivAt
  have outer := (UpperHalfPlane.hasStrictFDerivAt_smul g (h • z)).hasFDerivAt
  have outer' : HasFDerivAt (fun w : ℂ => (((g) • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ))
      (UpperHalfPlane.smulFDeriv g ((h • z : UpperHalfPlane) : ℂ))
      ((fun w : ℂ => (((h) • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)) (z : ℂ)) := by
    simpa only [UpperHalfPlane.ofComplex_apply] using outer
  have composite := outer'.comp (z : ℂ) inner
  have whole := (UpperHalfPlane.hasStrictFDerivAt_smul (g * h) z).hasFDerivAt
  have composite' : HasFDerivAt
      (fun w : ℂ => (((g * h) • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ))
      ((UpperHalfPlane.smulFDeriv g ((h • z : UpperHalfPlane) : ℂ)).comp
        (UpperHalfPlane.smulFDeriv h (z : ℂ))) (z : ℂ) := by
    refine composite.congr_of_eventuallyEq ?_
    filter_upwards with w
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply, mul_smul]
  exact whole.unique composite'

theorem smulFDeriv_mul_of_smul_I (g h : BinaryRealGL) (hh : h • UpperHalfPlane.I = UpperHalfPlane.I) :
    UpperHalfPlane.smulFDeriv (g * h) Complex.I =
      (UpperHalfPlane.smulFDeriv g Complex.I).comp (UpperHalfPlane.smulFDeriv h Complex.I) := by
  have chain := smulFDeriv_mul_base g h UpperHalfPlane.I
  rwa [hh, UpperHalfPlane.coe_I] at chain

theorem smulFDeriv_scalar_base (u : ℝˣ) :
    UpperHalfPlane.smulFDeriv (GeneralLinearGroup.scalar (Fin 2) u) Complex.I =
      ContinuousLinearMap.id ℝ ℂ := by
  have strict := (UpperHalfPlane.hasStrictFDerivAt_smul (GeneralLinearGroup.scalar (Fin 2) u)
    UpperHalfPlane.I).hasFDerivAt
  have identity : HasFDerivAt (fun w : ℂ =>
      ((GeneralLinearGroup.scalar (Fin 2) u • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ))
      (ContinuousLinearMap.id ℝ ℂ) ((UpperHalfPlane.I : UpperHalfPlane) : ℂ) := by
    refine (hasFDerivAt_id ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
      (show ((UpperHalfPlane.I : UpperHalfPlane) : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet from
        UpperHalfPlane.I.im_pos)] with w member
    show ((GeneralLinearGroup.scalar (Fin 2) u • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ) = w
    rw [UpperHalfPlane.glScalar_smul, UpperHalfPlane.ofComplex_apply_of_im_pos member]
  rw [UpperHalfPlane.coe_I] at strict identity
  exact strict.unique identity

end Geometry

section Algebra

variable (σ : CuspidalRepresentation) (n : ℕ)

theorem eichler_rho_mul (spherical : SphericalCusp σ) (A B : BinaryRealGL)
    (x : Fin (n + 2) → σ.H) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (A * B) x =
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A
        (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) B x) := by
  rw [binaryHilbertOperator_mul σ spherical (binaryWeightBasis (n + 1)) A B]
  rfl

theorem eichler_rho_one (spherical : SphericalCusp σ) (x : Fin (n + 2) → σ.H) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) 1 x = x := by
  rw [binaryHilbertOperator_one σ spherical (binaryWeightBasis (n + 1))]
  rfl

theorem eichler_J_mul_J : (UpperHalfPlane.J * UpperHalfPlane.J : BinaryRealGL) = 1 := by
  rw [← pow_two]
  exact UpperHalfPlane.J_sq

theorem eichler_rho_J_J (spherical : SphericalCusp σ) (x : Fin (n + 2) → σ.H) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
      (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J x) = x := by
  rw [← eichler_rho_mul σ n spherical, eichler_J_mul_J, eichler_rho_one σ n spherical]

theorem eichler_J_mul_rotation (θ : Circle) :
    UpperHalfPlane.J * binaryRotations θ = binaryRotations θ⁻¹ * UpperHalfPlane.J := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryRotations, binaryRotation, UpperHalfPlane.val_J, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem binaryCoefficient_scalar (u : ℝˣ) (v : Binary.HomogeneousPoly (n + 1)) :
    binaryCoefficient n (GeneralLinearGroup.scalar (Fin 2) u) v =
      ((u.val : ℂ)⁻¹) ^ (n + 3) • v := by
  unfold binaryCoefficient
  rw [GeneralLinearGroup.map_scalar, binary_homogeneousAction_scalar]
  simp only [Units.coe_map, MonoidHom.coe_ofClass, Complex.coe_algebraMap, Nat.add_assoc,
    show (1 : ℕ) + 2 = 3 from rfl]

/-- A positive real scalar acts trivially on tuples of a representation whose central character
is trivial on the positive reals. -/
theorem eichler_rho_scalar (spherical : SphericalCusp σ)
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
      cuspUnitary_positive_scalar σ spherical central_positive u hu, smul_smul,
      ← mul_pow, mul_inv_cancel₀ u_ne, one_pow, one_smul]
  · intro source _ different
    rw [binaryCoefficient_scalar, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, ite_eq_right different, smul_zero, zero_smul]
  · intro absent
    exact absurd (Finset.mem_univ _) absent

/-- The real-linear tangent vector `½ (d e - conj d · J e)`. -/
def eichlerTangent (e : Fin (n + 2) → σ.H) (d : ℂ) : Fin (n + 2) → σ.H :=
  (2 : ℂ)⁻¹ • (d • e - (starRingEnd ℂ d) •
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J e)

theorem eichlerTangent_reflection (spherical : SphericalCusp σ) (e : Fin (n + 2) → σ.H) (d : ℂ) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J (eichlerTangent σ n e d) =
      eichlerTangent σ n e (-(starRingEnd ℂ d)) := by
  unfold eichlerTangent
  simp only [map_smul, map_sub, eichler_rho_J_J σ n spherical, map_neg, Complex.conj_conj]
  module

theorem eichler_rho_rotation_J (spherical : SphericalCusp σ) (e : Fin (n + 2) → σ.H)
    (hrot : ∀ θ : Circle, binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) e =
      ((θ : ℂ) ^ 2)⁻¹ • e) (θ : Circle) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ)
        (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J e) =
      (θ : ℂ) ^ 2 • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J e := by
  have comm : binaryRotations θ * UpperHalfPlane.J = UpperHalfPlane.J * binaryRotations θ⁻¹ := by
    have := eichler_J_mul_rotation θ⁻¹
    rw [inv_inv] at this
    exact this.symm
  rw [← eichler_rho_mul σ n spherical, comm, eichler_rho_mul σ n spherical, hrot θ⁻¹, map_smul,
    circle_coe_inv, inv_pow, inv_inv]

theorem eichlerTangent_rotation (spherical : SphericalCusp σ) (e : Fin (n + 2) → σ.H)
    (hrot : ∀ θ : Circle, binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) e =
      ((θ : ℂ) ^ 2)⁻¹ • e) (θ : Circle) (d : ℂ) :
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ)
        (eichlerTangent σ n e d) =
      eichlerTangent σ n e (((θ : ℂ) ^ 2)⁻¹ * d) := by
  have hJ := eichler_rho_rotation_J σ n spherical e hrot θ
  have hc : starRingEnd ℂ (((θ : ℂ) ^ 2)⁻¹ * d) = (θ : ℂ) ^ 2 * starRingEnd ℂ d := by
    rw [map_mul, map_inv₀, map_pow, circle_conj_eq_inv, inv_pow, inv_inv]
  unfold eichlerTangent
  simp only [map_smul, map_sub, hrot θ, hJ, hc]
  module

/-- **Equivariance of the tangent vector under the stabilizer of `i`.** -/
theorem eichlerTangent_stabilizer (spherical : SphericalCusp σ)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (e : Fin (n + 2) → σ.H)
    (hrot : ∀ θ : Circle, binaryHilbertOperator σ (binaryWeightBasis (n + 1)) (binaryRotations θ) e =
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
      eichler_rho_mul σ n spherical, eichlerTangent_rotation σ n spherical e hrot θ d]
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
    rw [hBC, eichler_rho_mul σ n spherical, eichlerTangent_reflection σ n spherical,
      positive_case C det_pos fix, smulFDeriv_mul_of_smul_I C UpperHalfPlane.J binaryReflection_smul_I,
      ContinuousLinearMap.comp_apply, binaryReflection_smulFDeriv]
  · exact positive_case B positive hB d

end Algebra

end TernaryPeriodPolynomials.SourceConstruction

end
