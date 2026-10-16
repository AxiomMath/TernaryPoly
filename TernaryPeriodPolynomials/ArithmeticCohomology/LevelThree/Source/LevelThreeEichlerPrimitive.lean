module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.LevelThreeEichlerTangent

@[expose] public section


/-!
# The level-three Eichler potential and its cocycle

Level-three version of SC's `EichlerPrimitive`.  The input is SC's sphericity-free `L3Input σ n`
(a holomorphic smooth weight `-(n + 3)` vector fixed by the level-three Levi level).  The
reflection-symmetrised Eichler potential `½ (Per z + J Per(-conj z))` of a vector `v`
(`ltePotential`, an explicit function of the vector, so that linearity in `v` is formal) satisfies
`P(A z) = P(A i) + ρ(A) P(z)`; hence `A ↦ P(A i)` (`lteCocycle`) is a `GL₂(ℝ)`-cocycle vanishing on
the stabilizer of `i`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThreeSource

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.SourceConstruction

/-- The reflection-symmetrised Eichler potential `½ (Per z + J Per(-conj z))` of a vector. -/
def ltePotential (σ : CuspidalRepresentation) (n : ℕ) (halfWeight : ℤ) (v : σ.H) (z : ℂ) :
    Fin (n + 2) → σ.H :=
  (2 : ℂ)⁻¹ • (binaryEndpointPeriod σ n halfWeight v z +
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
      (binaryEndpointPeriod σ n halfWeight v (binaryComplexReflection z)))

/-- The Hilbert-level Eichler cocycle `A ↦ P(A · i)` of a vector. -/
def lteCocycle (σ : CuspidalRepresentation) (n : ℕ) (halfWeight : ℤ) (v : σ.H)
    (A : BinaryRealGL) : Fin (n + 2) → σ.H :=
  ltePotential σ n halfWeight v (basePoint A)

section Potential

variable {σ : CuspidalRepresentation} {n : ℕ} (D : L3Input σ n)

/-- The potential of the input vector of `D`. -/
def ltePot : ℂ → Fin (n + 2) → σ.H :=
  ltePotential σ n D.halfWeight D.vector.val

/-- **The potential is real differentiable with the Eichler differential as derivative.** -/
theorem ltePot_hasFDerivAt (z : ℂ) (hz : 0 < z.im) :
    ∃ L : ℂ →L[ℝ] (Fin (n + 2) → σ.H), HasFDerivAt (ltePot D) L z ∧
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
  have formula := lte_endpointDifferential_holomorphicForm σ D.cusp3 n D.halfWeight D.weight
    D.vector.val z hz d
  change _ = binaryEndpointDifferential σ (binaryWeightBasis (n + 1)) (Pi.single 0 D.vector.val)
    z d
  rw [formula]
  show (2 : ℂ)⁻¹ • (d • binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val z +
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
        (binaryComplexReflection d • binaryEndpointHolomorphicForm σ n D.halfWeight
          D.vector.val (binaryComplexReflection z))) = _
  rw [reflection_d, map_smul, neg_smul, ← sub_eq_add_neg]

theorem ltePot_I : ltePot D Complex.I = 0 := by
  unfold ltePot ltePotential
  rw [binaryComplexReflection_basepoint, D.period_I, map_zero, add_zero, smul_zero]

/-- **The potential is affine-equivariant.** -/
theorem ltePot_affine (A : BinaryRealGL) (p : UpperHalfPlane) :
    ltePot D ((A • p : UpperHalfPlane) : ℂ) =
      ltePot D ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
        binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A (ltePot D (p : ℂ)) := by
  let ρA := (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A).restrictScalars ℝ
  let G : ℂ → (Fin (n + 2) → σ.H) := fun w =>
    ltePot D ((A • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ) - ρA (ltePot D w)
  have deriv_zero : ∀ w ∈ UpperHalfPlane.upperHalfPlaneSet,
      HasFDerivAt G (0 : ℂ →L[ℝ] (Fin (n + 2) → σ.H)) w := by
    intro w hw
    let q : UpperHalfPlane := ⟨w, hw⟩
    obtain ⟨L1, hL1, hL1d⟩ := ltePot_hasFDerivAt D ((A • q : UpperHalfPlane) : ℂ)
      (A • q).im_pos
    obtain ⟨L2, hL2, hL2d⟩ := ltePot_hasFDerivAt D (q : ℂ) q.im_pos
    have orbit : HasFDerivAt
        (fun x : ℂ => ((A • UpperHalfPlane.ofComplex x : UpperHalfPlane) : ℂ))
        (UpperHalfPlane.smulFDeriv A (q : ℂ)) (q : ℂ) :=
      (UpperHalfPlane.hasStrictFDerivAt_smul A q).hasFDerivAt
    have hL1' : HasFDerivAt (ltePot D) L1
        ((fun x : ℂ => ((A • UpperHalfPlane.ofComplex x : UpperHalfPlane) : ℂ)) (q : ℂ)) := by
      simpa only [UpperHalfPlane.ofComplex_apply] using hL1
    have first := hL1'.comp (q : ℂ) orbit
    have second := ρA.hasFDerivAt.comp (q : ℂ) hL2
    have both := first.sub second
    have zero : L1.comp (UpperHalfPlane.smulFDeriv A (q : ℂ)) - ρA.comp L2 = 0 := by
      ext d
      simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, _root_.zero_apply]
      rw [hL1d, hL2d, lte_differential_equivariant σ n D.cusp3 D.central_positive D.lower
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
  rw [UpperHalfPlane.coe_I, ltePot_I, map_zero, sub_zero] at constant
  exact sub_eq_iff_eq_add.mp constant

/-- The Hilbert-level Eichler cocycle of the input vector of `D`. -/
def lteCoc (A : BinaryRealGL) : Fin (n + 2) → σ.H := ltePot D (basePoint A)

theorem lteCoc_eq (A : BinaryRealGL) :
    lteCoc D A = lteCocycle σ n D.halfWeight D.vector.val A := rfl

/-- **The cocycle identity.** -/
theorem lteCoc_mul (A B : BinaryRealGL) :
    lteCoc D (A * B) = lteCoc D A +
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A (lteCoc D B) := by
  unfold lteCoc basePoint
  rw [mul_smul]
  exact ltePot_affine D A (B • UpperHalfPlane.I)

/-- **The cocycle vanishes on the stabilizer of `i`.** -/
theorem lteCoc_eq_zero_of_smul_I (A : BinaryRealGL)
    (h : A • UpperHalfPlane.I = UpperHalfPlane.I) : lteCoc D A = 0 := by
  unfold lteCoc basePoint
  rw [h, UpperHalfPlane.coe_I]
  exact ltePot_I D

end Potential

end TernaryPeriodPolynomials.LevelThreeSource

end
