module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerRho
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Primitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.EichlerTwPrimitive

@[expose] public section


/-!
# The level-three sign-twisted Eichler potential and its cocycle

The input of the construction is a smooth holomorphic weight vector `-(n + 3)` fixed by the
level-three Levi level (`levelThreeValues`).  Its straight-line Eichler period `Per` is a primitive
of the holomorphic form, the antisymmetrised potential `P⁻(z) = ½ (Per z - J Per(-z̄))` satisfies
`P⁻(A z) = P⁻(A i) + sgn(det A) ρ(A) P⁻(z)`, and `A ↦ P⁻(A i)` is a sign-twisted cocycle
vanishing on the stabilizer of `i`.  The potential is written as an explicit function of the
vector, `l3Potential`, so that linearity in the vector is a formal consequence.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.MultiplicityOne (LevelThreeCusp levelThreeValues)

/-- The input of the level-three Eichler construction: a smooth holomorphic lowest-weight vector
of weight `-(n + 3)` fixed by the level-three Levi level, in a cuspidal representation whose
central character is trivial on the positive reals. -/
structure L3Input (σ : CuspidalRepresentation) (n : ℕ) where
  central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1
  cusp3 : LevelThreeCusp σ
  halfWeight : ℤ
  weight : 2 * halfWeight = -((n : ℤ) + 3)
  vector : σ.smooth
  vector_level : vector.val ∈ levelThreeValues σ
  rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) vector.val =
    (angle : ℂ) ^ (2 * halfWeight) • vector.val
  holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit σ halfWeight vector.val)
    UpperHalfPlane.upperHalfPlaneSet

/-- The reflection-antisymmetrised Eichler potential `½ (Per z - J Per(-conj z))` of a vector. -/
def l3Potential (σ : CuspidalRepresentation) (n : ℕ) (halfWeight : ℤ) (v : σ.H) (z : ℂ) :
    Fin (n + 2) → σ.H :=
  (2 : ℂ)⁻¹ • (binaryEndpointPeriod σ n halfWeight v z -
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
      (binaryEndpointPeriod σ n halfWeight v (binaryComplexReflection z)))

/-- The twisted Hilbert-level Eichler cocycle `A ↦ P⁻(A · i)` of a vector. -/
def l3Cocycle (σ : CuspidalRepresentation) (n : ℕ) (halfWeight : ℤ) (v : σ.H)
    (A : BinaryRealGL) : Fin (n + 2) → σ.H :=
  l3Potential σ n halfWeight v (basePoint A)

namespace L3Input

variable {σ : CuspidalRepresentation} {n : ℕ} (D : L3Input σ n)

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

theorem period_I : binaryEndpointPeriod σ n D.halfWeight D.vector.val Complex.I = 0 := by
  unfold binaryEndpointPeriod
  simp

/-- The twisted potential of the input vector. -/
def potential (z : ℂ) : Fin (n + 2) → σ.H :=
  l3Potential σ n D.halfWeight D.vector.val z

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
  have formula := l3_endpointDifferentialTw_holomorphicForm σ D.cusp3 n D.halfWeight D.weight
    D.vector.val z hz d
  change _ = binaryEndpointDifferentialTw σ (binaryWeightBasis (n + 1)) (Pi.single 0 D.vector.val) z d
  rw [formula]
  show (2 : ℂ)⁻¹ • (d • binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val z -
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
        (binaryComplexReflection d • binaryEndpointHolomorphicForm σ n D.halfWeight
          D.vector.val (binaryComplexReflection z))) = _
  rw [reflection_d, map_smul, neg_smul, sub_neg_eq_add]

theorem potential_fderiv (z : ℂ) (hz : 0 < z.im) (d : ℂ) :
    fderiv ℝ D.potential z d =
      binaryEndpointDifferentialTw σ (binaryWeightBasis (n + 1)) D.lower z d := by
  obtain ⟨L, hL, hLd⟩ := D.potential_hasFDerivAt z hz
  rw [hL.fderiv, hLd]

theorem potential_I : D.potential Complex.I = 0 := by
  unfold L3Input.potential l3Potential
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
    D.cocycle A = l3Cocycle σ n D.halfWeight D.vector.val A := rfl

/-- **The twisted cocycle identity.** -/
theorem cocycle_mul (A B : BinaryRealGL) :
    D.cocycle (A * B) = D.cocycle A +
      signDet A • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A (D.cocycle B) := by
  unfold L3Input.cocycle basePoint
  rw [mul_smul]
  exact D.potential_affine A (B • UpperHalfPlane.I)

/-- **The twisted cocycle vanishes on the stabilizer of `i`.** -/
theorem cocycle_eq_zero_of_smul_I (A : BinaryRealGL)
    (h : A • UpperHalfPlane.I = UpperHalfPlane.I) : D.cocycle A = 0 := by
  unfold L3Input.cocycle basePoint
  rw [h, UpperHalfPlane.coe_I]
  exact D.potential_I

end L3Input

end TernaryPeriodPolynomials.SourceConstruction

end
