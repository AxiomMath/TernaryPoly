module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Primitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.EichlerTwTangent

@[expose] public section


/-!
# The twisted Eichler potential and its cocycle

For the odd quadratic character the Levi `GL₂` acts through the sign-twisted representation
`signDet A • ρ(A)`.  The antisymmetrised potential `P⁻(z) = ½ (Per z - ρ(J) Per(-conj z))` is a
primitive of the twisted Eichler differential, satisfies
`P⁻(A z) = P⁻(A i) + signDet A • ρ(A) P⁻(z)`, and so `A ↦ P⁻(A i)` is a twisted
`GL₂(ℝ)`-cocycle vanishing on the stabilizer of `i`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.TwistedSource

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.SourceConstruction

section Primitive

variable {σ : CuspidalRepresentation} {n : ℕ} (D : EichlerInput σ n)

/-- The reflection-antisymmetrised Eichler potential `½ (Per z - J Per(-conj z))`. -/
def potentialTw (z : ℂ) : Fin (n + 2) → σ.H :=
  (2 : ℂ)⁻¹ • (binaryEndpointPeriod σ n D.halfWeight D.vector.val z -
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
      (binaryEndpointPeriod σ n D.halfWeight D.vector.val (binaryComplexReflection z)))

/-- **The twisted potential is real differentiable with the twisted Eichler differential as
derivative.** -/
theorem potentialTw_hasFDerivAt (z : ℂ) (hz : 0 < z.im) :
    ∃ L : ℂ →L[ℝ] (Fin (n + 2) → σ.H), HasFDerivAt (potentialTw D) L z ∧
      ∀ d : ℂ, L d = binaryEndpointDifferentialTw σ (binaryWeightBasis (n + 1)) D.lower z d := by
  have hz' : 0 < (binaryComplexReflection z).im := by rwa [binaryComplexReflection_im]
  have h1 := (D.period_hasDerivAt z hz).hasFDerivAt.restrictScalars ℝ
  have h2' := (D.period_hasDerivAt (binaryComplexReflection z) hz').hasFDerivAt.restrictScalars ℝ
  have h2 := h2'.comp z binaryComplexReflection.hasFDerivAt
  have h3 := ((binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J).restrictScalars
    ℝ).hasFDerivAt.comp z h2
  have h4 := (h1.sub h3).const_smul (2 : ℂ)⁻¹
  refine ⟨_, h4.congr_of_eventuallyEq (by filter_upwards with x; rfl), fun d => ?_⟩
  have reflection_d : binaryComplexReflection d = -(starRingEnd ℂ d) := by
    simp [binaryComplexReflection]
  have formula := binaryEndpointDifferentialTw_holomorphicForm σ D.spherical n D.halfWeight D.weight
    D.vector.val z hz d
  change _ = binaryEndpointDifferentialTw σ (binaryWeightBasis (n + 1)) (Pi.single 0 D.vector.val) z d
  rw [formula]
  show (2 : ℂ)⁻¹ • (d • binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val z -
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
        (binaryComplexReflection d • binaryEndpointHolomorphicForm σ n D.halfWeight
          D.vector.val (binaryComplexReflection z))) = _
  rw [reflection_d, map_smul, neg_smul, sub_neg_eq_add]

theorem potentialTw_fderiv (z : ℂ) (hz : 0 < z.im) (d : ℂ) :
    fderiv ℝ (potentialTw D) z d =
      binaryEndpointDifferentialTw σ (binaryWeightBasis (n + 1)) D.lower z d := by
  obtain ⟨L, hL, hLd⟩ := potentialTw_hasFDerivAt D z hz
  rw [hL.fderiv, hLd]

theorem potentialTw_I : potentialTw D Complex.I = 0 := by
  unfold potentialTw
  rw [binaryComplexReflection_basepoint, D.period_I, map_zero, sub_self, smul_zero]

/-- **The twisted potential is affine-equivariant.** -/
theorem potentialTw_affine (A : BinaryRealGL) (p : UpperHalfPlane) :
    potentialTw D ((A • p : UpperHalfPlane) : ℂ) =
      potentialTw D ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
        signDet A • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A
          (potentialTw D (p : ℂ)) := by
  let ρA : (Fin (n + 2) → σ.H) →L[ℝ] (Fin (n + 2) → σ.H) :=
    (signDet A • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A).restrictScalars ℝ
  let G : ℂ → (Fin (n + 2) → σ.H) := fun w =>
    potentialTw D ((A • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ) - ρA (potentialTw D w)
  have deriv_zero : ∀ w ∈ UpperHalfPlane.upperHalfPlaneSet,
      HasFDerivAt G (0 : ℂ →L[ℝ] (Fin (n + 2) → σ.H)) w := by
    intro w hw
    let q : UpperHalfPlane := ⟨w, hw⟩
    obtain ⟨L1, hL1, hL1d⟩ := potentialTw_hasFDerivAt D ((A • q : UpperHalfPlane) : ℂ)
      (A • q).im_pos
    obtain ⟨L2, hL2, hL2d⟩ := potentialTw_hasFDerivAt D (q : ℂ) q.im_pos
    have orbit : HasFDerivAt
        (fun x : ℂ => ((A • UpperHalfPlane.ofComplex x : UpperHalfPlane) : ℂ))
        (UpperHalfPlane.smulFDeriv A (q : ℂ)) (q : ℂ) :=
      (UpperHalfPlane.hasStrictFDerivAt_smul A q).hasFDerivAt
    have hL1' : HasFDerivAt (potentialTw D) L1
        ((fun x : ℂ => ((A • UpperHalfPlane.ofComplex x : UpperHalfPlane) : ℂ)) (q : ℂ)) := by
      simpa only [UpperHalfPlane.ofComplex_apply] using hL1
    have first := hL1'.comp (q : ℂ) orbit
    have second := ρA.hasFDerivAt.comp (q : ℂ) hL2
    have both := first.sub second
    have zero : L1.comp (UpperHalfPlane.smulFDeriv A (q : ℂ)) - ρA.comp L2 = 0 := by
      ext d
      simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, _root_.zero_apply]
      rw [hL1d, hL2d, eichlerDifferentialTw_equivariant σ n D.spherical D.central_positive D.lower
        D.lower_rotation A q d]
      exact sub_self _
    rw [zero] at both
    exact both
  have convex : Convex ℝ UpperHalfPlane.upperHalfPlaneSet :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm
  have constant : G (p : ℂ) = G (UpperHalfPlane.I : ℂ) :=
    UpperHalfPlane.isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero convex.isPreconnected
      (fun w hw => (deriv_zero w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (deriv_zero w hw).fderiv) p.im_pos UpperHalfPlane.I.im_pos
  simp only [G, UpperHalfPlane.ofComplex_apply] at constant
  rw [UpperHalfPlane.coe_I, potentialTw_I, map_zero, sub_zero] at constant
  exact sub_eq_iff_eq_add.mp constant

/-- The twisted Hilbert-level Eichler cocycle `A ↦ P⁻(A · i)`. -/
def cocycleTw (A : BinaryRealGL) : Fin (n + 2) → σ.H := potentialTw D (basePoint A)

/-- **The twisted cocycle identity.** -/
theorem cocycleTw_mul (A B : BinaryRealGL) :
    cocycleTw D (A * B) = cocycleTw D A +
      signDet A • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A (cocycleTw D B) := by
  unfold cocycleTw basePoint
  rw [mul_smul]
  exact potentialTw_affine D A (B • UpperHalfPlane.I)

/-- **The twisted cocycle vanishes on the stabilizer of `i`.** -/
theorem cocycleTw_eq_zero_of_smul_I (A : BinaryRealGL)
    (h : A • UpperHalfPlane.I = UpperHalfPlane.I) : cocycleTw D A = 0 := by
  unfold cocycleTw basePoint
  rw [h, UpperHalfPlane.coe_I]
  exact potentialTw_I D

end Primitive

end TernaryPeriodPolynomials.TwistedSource

end
