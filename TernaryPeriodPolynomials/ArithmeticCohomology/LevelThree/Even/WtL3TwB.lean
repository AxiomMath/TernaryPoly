module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwA

@[expose] public section


/-!
# Weight-generic level-three Eichler input, second half

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins of the remainder of `L3EichlerPrimitive` for `L3InputWt`: the antisymmetrised potential is
real differentiable with the twisted Eichler differential as derivative, it is affine-equivariant,
and its values at the images of `i` form a sign-twisted cocycle vanishing on the stabilizer of `i`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.SourceConstruction
  (l3_eichlerDifferentialTw_equivariant)

namespace L3InputWt

variable {σ : CuspidalRepresentation} {n : ℕ} (D : L3InputWt σ n)

theorem period_I : binaryEndpointPeriodWt σ n D.wt D.vector.val Complex.I = 0 := by
  unfold binaryEndpointPeriodWt
  simp

/-- The twisted potential of the input vector. -/
def potential (z : ℂ) : Fin (n + 2) → σ.H :=
  l3PotentialWt σ n D.wt D.vector.val z

/-- **The twisted potential is real differentiable with the twisted Eichler differential as
derivative.** -/
theorem potential_hasFDerivAt (z : ℂ) (hz : 0 < z.im) :
    ∃ L : ℂ →L[ℝ] (Fin (n + 2) → σ.H), HasFDerivAt D.potential L z ∧
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
  have formula := l3_endpointDifferentialTw_holomorphicFormWt σ D.cusp3 n D.wt D.weight
    D.vector.val z hz d
  change _ = binaryEndpointDifferentialTw σ (binaryWeightBasis (n + 1)) (Pi.single 0 D.vector.val) z d
  rw [formula]
  show (2 : ℂ)⁻¹ • (d • binaryEndpointHolomorphicFormWt σ n D.wt D.vector.val z -
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
        (binaryComplexReflection d • binaryEndpointHolomorphicFormWt σ n D.wt
          D.vector.val (binaryComplexReflection z))) = _
  rw [reflection_d, map_smul, neg_smul, sub_neg_eq_add]

theorem potential_fderiv (z : ℂ) (hz : 0 < z.im) (d : ℂ) :
    fderiv ℝ D.potential z d =
      binaryEndpointDifferentialTw σ (binaryWeightBasis (n + 1)) D.lower z d := by
  obtain ⟨L, hL, hLd⟩ := D.potential_hasFDerivAt z hz
  rw [hL.fderiv, hLd]

theorem potential_I : D.potential Complex.I = 0 := by
  unfold L3InputWt.potential l3PotentialWt
  rw [binaryComplexReflection_basepoint, D.period_I, map_zero, sub_self, smul_zero]

/-- **The twisted potential is affine-equivariant.** -/
theorem potential_affine (A : BinaryRealGL) (p : UpperHalfPlane) :
    D.potential ((A • p : UpperHalfPlane) : ℂ) =
      D.potential ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
        signDet A • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A
          (D.potential (p : ℂ)) := by
  let ρA : (Fin (n + 2) → σ.H) →L[ℝ] (Fin (n + 2) → σ.H) :=
    (signDet A • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A).restrictScalars ℝ
  let G : ℂ → (Fin (n + 2) → σ.H) := fun w =>
    D.potential ((A • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ) - ρA (D.potential w)
  have deriv_zero : ∀ w ∈ UpperHalfPlane.upperHalfPlaneSet,
      HasFDerivAt G (0 : ℂ →L[ℝ] (Fin (n + 2) → σ.H)) w := by
    intro w hw
    let q : UpperHalfPlane := ⟨w, hw⟩
    obtain ⟨L1, hL1, hL1d⟩ := D.potential_hasFDerivAt ((A • q : UpperHalfPlane) : ℂ)
      (A • q).im_pos
    obtain ⟨L2, hL2, hL2d⟩ := D.potential_hasFDerivAt (q : ℂ) q.im_pos
    have orbit : HasFDerivAt
        (fun x : ℂ => ((A • UpperHalfPlane.ofComplex x : UpperHalfPlane) : ℂ))
        (UpperHalfPlane.smulFDeriv A (q : ℂ)) (q : ℂ) :=
      (UpperHalfPlane.hasStrictFDerivAt_smul A q).hasFDerivAt
    have hL1' : HasFDerivAt D.potential L1
        ((fun x : ℂ => ((A • UpperHalfPlane.ofComplex x : UpperHalfPlane) : ℂ)) (q : ℂ)) := by
      simpa only [UpperHalfPlane.ofComplex_apply] using hL1
    have first := hL1'.comp (q : ℂ) orbit
    have second := ρA.hasFDerivAt.comp (q : ℂ) hL2
    have both := first.sub second
    have zero : L1.comp (UpperHalfPlane.smulFDeriv A (q : ℂ)) - ρA.comp L2 = 0 := by
      ext d
      simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, _root_.zero_apply]
      rw [hL1d, hL2d, l3_eichlerDifferentialTw_equivariant σ n D.cusp3 D.central_positive D.lower
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
  rw [UpperHalfPlane.coe_I, D.potential_I, map_zero, sub_zero] at constant
  exact sub_eq_iff_eq_add.mp constant

/-- The twisted Hilbert-level Eichler cocycle `A ↦ P⁻(A · i)`. -/
def cocycle (A : BinaryRealGL) : Fin (n + 2) → σ.H := D.potential (basePoint A)

theorem cocycle_eq_l3Cocycle (A : BinaryRealGL) :
    D.cocycle A = l3CocycleWt σ n D.wt D.vector.val A := rfl

/-- **The twisted cocycle identity.** -/
theorem cocycle_mul (A B : BinaryRealGL) :
    D.cocycle (A * B) = D.cocycle A +
      signDet A • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A (D.cocycle B) := by
  unfold L3InputWt.cocycle basePoint
  rw [mul_smul]
  exact D.potential_affine A (B • UpperHalfPlane.I)

/-- **The twisted cocycle vanishes on the stabilizer of `i`.** -/
theorem cocycle_eq_zero_of_smul_I (A : BinaryRealGL)
    (h : A • UpperHalfPlane.I = UpperHalfPlane.I) : D.cocycle A = 0 := by
  unfold L3InputWt.cocycle basePoint
  rw [h, UpperHalfPlane.coe_I]
  exact D.potential_I

end L3InputWt

end TernaryPeriodPolynomials.EvenLevelThree

end
