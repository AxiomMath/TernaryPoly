module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Equivariance

@[expose] public section


/-!
# The Eichler potential and its cocycle

For a holomorphic lowest-weight vector, the straight-line Eichler period `Per` of the
holomorphic form is a primitive on the upper half plane, and
`P(z) = ½ (Per z + J Per(-conj z))` is a primitive of the equivariant Eichler differential.
Equivariance forces `P(A z) = P(A i) + ρ(A) P(z)`, hence `A ↦ P(A i)` is a `GL₂(ℝ)`-cocycle
vanishing on the stabilizer of `i`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

namespace EichlerInput

variable {σ : CuspidalRepresentation} {n : ℕ} (D : EichlerInput σ n)

theorem form_differentiableOn :
    DifferentiableOn ℂ (binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val)
      UpperHalfPlane.upperHalfPlaneSet := by
  rw [differentiableOn_pi]
  intro position
  have scalar : Differentiable ℂ (fun z : ℂ =>
      (binaryWeightBasis (n + 1)).coord position (binaryPointPower (n + 1) z)) := fun z =>
    (binaryPointPower_functional_analytic (n + 1) ((binaryWeightBasis (n + 1)).coord position)
      z).differentiableAt
  exact scalar.differentiableOn.smul D.holomorphic

/-- **The Eichler period is a primitive of the holomorphic form.** -/
theorem period_hasDerivAt (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (binaryEndpointPeriod σ n D.halfWeight D.vector.val)
      (binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val z) z := by
  have convex : Convex ℝ UpperHalfPlane.upperHalfPlaneSet :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm
  obtain ⟨F, hF⟩ := convex.exists_forall_hasDerivWithinAt D.form_differentiableOn
  have hFat : ∀ a ∈ UpperHalfPlane.upperHalfPlaneSet,
      HasDerivAt F (binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val a) a :=
    fun a ha => (hF a ha).hasDerivAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds ha)
  have period : ∀ x : ℂ, 0 < x.im →
      binaryEndpointPeriod σ n D.halfWeight D.vector.val x = F x - F Complex.I := by
    intro x hx
    have path_derivative : ∀ t : ℝ,
        HasDerivAt (fun t : ℝ => Complex.I + t • (x - Complex.I)) (x - Complex.I) t := by
      intro t
      simpa only [one_smul, id_eq] using
        ((hasDerivAt_id t).smul_const (x - Complex.I)).const_add Complex.I
    have derivative : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => F (Complex.I + t • (x - Complex.I)))
          ((x - Complex.I) • binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val
            (Complex.I + t • (x - Complex.I))) t := by
      intro t ht
      have belongs : t ∈ Set.Icc (0 : ℝ) 1 := by simpa only [Set.uIcc_of_le zero_le_one] using ht
      exact (hFat _ (upperHalfPlane_straightPath ⟨x, hx⟩ belongs)).scomp t (path_derivative t)
    have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative
      (binaryEndpointPeriod_integrable σ n D.halfWeight D.vector.val x hx)
    unfold binaryEndpointPeriod
    rw [integral]
    simp only [one_smul, zero_smul, add_zero, add_sub_cancel]
  have h1 : HasDerivAt (fun x => F x - F Complex.I)
      (binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val z) z :=
    (hFat z (show z ∈ UpperHalfPlane.upperHalfPlaneSet from hz)).sub_const (F Complex.I)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
    (show z ∈ UpperHalfPlane.upperHalfPlaneSet from hz)] with x hx
  exact period x hx

/-- The reflection-symmetrised Eichler potential `½ (Per z + J Per(-conj z))`. -/
def potential (z : ℂ) : Fin (n + 2) → σ.H :=
  (2 : ℂ)⁻¹ • (binaryEndpointPeriod σ n D.halfWeight D.vector.val z +
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
      (binaryEndpointPeriod σ n D.halfWeight D.vector.val (binaryComplexReflection z)))

/-- **The potential is real differentiable with the Eichler differential as derivative.** -/
theorem potential_hasFDerivAt (z : ℂ) (hz : 0 < z.im) :
    ∃ L : ℂ →L[ℝ] (Fin (n + 2) → σ.H), HasFDerivAt D.potential L z ∧
      ∀ d : ℂ, L d = binaryEndpointDifferential σ (binaryWeightBasis (n + 1)) D.lower z d := by
  have hz' : 0 < (binaryComplexReflection z).im := by rwa [binaryComplexReflection_im]
  have h1 := (D.period_hasDerivAt z hz).hasFDerivAt.restrictScalars ℝ
  have h2' := (D.period_hasDerivAt (binaryComplexReflection z) hz').hasFDerivAt.restrictScalars ℝ
  have h2 := h2'.comp z binaryComplexReflection.hasFDerivAt
  have h3 := ((binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J).restrictScalars
    ℝ).hasFDerivAt.comp z h2
  have h4 := (h1.add h3).const_smul (2 : ℂ)⁻¹
  refine ⟨_, h4.congr_of_eventuallyEq (by filter_upwards with x; rfl), fun d => ?_⟩
  have reflection_d : binaryComplexReflection d = -(starRingEnd ℂ d) := by
    simp [binaryComplexReflection]
  have formula := binaryEndpointDifferential_holomorphicForm σ D.spherical n D.halfWeight D.weight
    D.vector.val z hz d
  change _ = binaryEndpointDifferential σ (binaryWeightBasis (n + 1)) (Pi.single 0 D.vector.val) z d
  rw [formula]
  show (2 : ℂ)⁻¹ • (d • binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val z +
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
        (binaryComplexReflection d • binaryEndpointHolomorphicForm σ n D.halfWeight
          D.vector.val (binaryComplexReflection z))) = _
  rw [reflection_d, map_smul, neg_smul, ← sub_eq_add_neg]

theorem potential_fderiv (z : ℂ) (hz : 0 < z.im) (d : ℂ) :
    fderiv ℝ D.potential z d =
      binaryEndpointDifferential σ (binaryWeightBasis (n + 1)) D.lower z d := by
  obtain ⟨L, hL, hLd⟩ := D.potential_hasFDerivAt z hz
  rw [hL.fderiv, hLd]

theorem period_I : binaryEndpointPeriod σ n D.halfWeight D.vector.val Complex.I = 0 := by
  unfold binaryEndpointPeriod
  simp

theorem potential_I : D.potential Complex.I = 0 := by
  unfold potential
  rw [binaryComplexReflection_basepoint, D.period_I, map_zero, add_zero, smul_zero]

/-- **The potential is affine-equivariant.** -/
theorem potential_affine (A : BinaryRealGL) (p : UpperHalfPlane) :
    D.potential ((A • p : UpperHalfPlane) : ℂ) =
      D.potential ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
        binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A (D.potential (p : ℂ)) := by
  let ρA := (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A).restrictScalars ℝ
  let G : ℂ → (Fin (n + 2) → σ.H) := fun w =>
    D.potential ((A • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ) - ρA (D.potential w)
  have deriv_zero : ∀ w ∈ UpperHalfPlane.upperHalfPlaneSet,
      HasFDerivAt G (0 : ℂ →L[ℝ] (Fin (n + 2) → σ.H)) w := by
    intro w hw
    let q : UpperHalfPlane := ⟨w, hw⟩
    obtain ⟨L1, hL1, hL1d⟩ := D.potential_hasFDerivAt ((A • q : UpperHalfPlane) : ℂ) (A • q).im_pos
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
      simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply,
        _root_.zero_apply]
      rw [hL1d, hL2d, eichlerDifferential_equivariant σ n D.spherical D.central_positive D.lower
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

/-- The Hilbert-level Eichler cocycle `A ↦ P(A · i)`. -/
def cocycle (A : BinaryRealGL) : Fin (n + 2) → σ.H := D.potential (basePoint A)

theorem cocycle_eq_hilbertNormal (A : BinaryRealGL) :
    D.cocycle A = hilbertNormal σ n D.halfWeight D.vector.val A := rfl

/-- **The cocycle identity.** -/
theorem cocycle_mul (A B : BinaryRealGL) :
    D.cocycle (A * B) = D.cocycle A +
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A (D.cocycle B) := by
  unfold cocycle basePoint
  rw [mul_smul]
  exact D.potential_affine A (B • UpperHalfPlane.I)

/-- **The cocycle vanishes on the stabilizer of `i`.** -/
theorem cocycle_eq_zero_of_smul_I (A : BinaryRealGL) (h : A • UpperHalfPlane.I = UpperHalfPlane.I) :
    D.cocycle A = 0 := by
  unfold cocycle basePoint
  rw [h, UpperHalfPlane.coe_I]
  exact D.potential_I

end EichlerInput

end TernaryPeriodPolynomials.SourceConstruction

end
