module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwB
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.L3UntwTangent

@[expose] public section


/-!
# Weight-generic level-three Eichler potential and cocycle, untwisted

Formalized by Claude Sonnet 5.5 (AxiomCode).

The untwisted twin of `WtL3TwA`/`WtL3TwB` and of `EichlerPrimitive` for an integer rotation weight
`wt = -(n + 3)` at level three.  The input datum is `L3InputWt` itself (the data are identical).
The reflection-symmetrised potential `P⁺(z) = ½ (Per z + J Per(-conj z))` is a primitive of the
equivariant Eichler differential, satisfies `P⁺(A z) = P⁺(A i) + ρ(A) P⁺(z)`, and its values
`A ↦ P⁺(A i)` form a `GL₂(ℝ)`-cocycle vanishing on the stabilizer of `i`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

/-- The reflection-symmetrised Eichler potential `½ (Per z + J Per(-conj z))` of a vector. -/
def l3PlanePotentialWt (σ : CuspidalRepresentation) (n : ℕ) (wt : ℤ) (v : σ.H) (z : ℂ) :
    Fin (n + 2) → σ.H :=
  (2 : ℂ)⁻¹ • (binaryEndpointPeriodWt σ n wt v z +
    binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
      (binaryEndpointPeriodWt σ n wt v (binaryComplexReflection z)))

/-- The untwisted Hilbert-level Eichler cocycle `A ↦ P⁺(A · i)` of a vector. -/
def l3PlaneCocycleWt (σ : CuspidalRepresentation) (n : ℕ) (wt : ℤ) (v : σ.H)
    (A : BinaryRealGL) : Fin (n + 2) → σ.H :=
  l3PlanePotentialWt σ n wt v (basePoint A)

namespace L3InputWt

variable {σ : CuspidalRepresentation} {n : ℕ} (D : L3InputWt σ n)

/-- The untwisted potential of the input vector. -/
def planePotential (z : ℂ) : Fin (n + 2) → σ.H :=
  l3PlanePotentialWt σ n D.wt D.vector.val z

/-- **The untwisted potential is real differentiable with the Eichler differential as
derivative.** -/
theorem planePotential_hasFDerivAt (z : ℂ) (hz : 0 < z.im) :
    ∃ L : ℂ →L[ℝ] (Fin (n + 2) → σ.H), HasFDerivAt D.planePotential L z ∧
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
  have formula := l3_endpointDifferential_holomorphicFormWt σ D.cusp3 n D.wt D.weight
    D.vector.val z hz d
  change _ = binaryEndpointDifferential σ (binaryWeightBasis (n + 1)) (Pi.single 0 D.vector.val) z d
  rw [formula]
  show (2 : ℂ)⁻¹ • (d • binaryEndpointHolomorphicFormWt σ n D.wt D.vector.val z +
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
        (binaryComplexReflection d • binaryEndpointHolomorphicFormWt σ n D.wt
          D.vector.val (binaryComplexReflection z))) = _
  rw [reflection_d, map_smul, neg_smul, ← sub_eq_add_neg]

theorem planePotential_fderiv (z : ℂ) (hz : 0 < z.im) (d : ℂ) :
    fderiv ℝ D.planePotential z d =
      binaryEndpointDifferential σ (binaryWeightBasis (n + 1)) D.lower z d := by
  obtain ⟨L, hL, hLd⟩ := D.planePotential_hasFDerivAt z hz
  rw [hL.fderiv, hLd]

theorem planePotential_I : D.planePotential Complex.I = 0 := by
  unfold L3InputWt.planePotential l3PlanePotentialWt
  rw [binaryComplexReflection_basepoint, D.period_I, map_zero, add_zero, smul_zero]

/-- **The untwisted potential is affine-equivariant.** -/
theorem planePotential_affine (A : BinaryRealGL) (p : UpperHalfPlane) :
    D.planePotential ((A • p : UpperHalfPlane) : ℂ) =
      D.planePotential ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
        binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A (D.planePotential (p : ℂ)) := by
  let ρA : (Fin (n + 2) → σ.H) →L[ℝ] (Fin (n + 2) → σ.H) :=
    (binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A).restrictScalars ℝ
  let G : ℂ → (Fin (n + 2) → σ.H) := fun w =>
    D.planePotential ((A • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ) -
      ρA (D.planePotential w)
  have deriv_zero : ∀ w ∈ UpperHalfPlane.upperHalfPlaneSet,
      HasFDerivAt G (0 : ℂ →L[ℝ] (Fin (n + 2) → σ.H)) w := by
    intro w hw
    let q : UpperHalfPlane := ⟨w, hw⟩
    obtain ⟨L1, hL1, hL1d⟩ := D.planePotential_hasFDerivAt ((A • q : UpperHalfPlane) : ℂ)
      (A • q).im_pos
    obtain ⟨L2, hL2, hL2d⟩ := D.planePotential_hasFDerivAt (q : ℂ) q.im_pos
    have orbit : HasFDerivAt
        (fun x : ℂ => ((A • UpperHalfPlane.ofComplex x : UpperHalfPlane) : ℂ))
        (UpperHalfPlane.smulFDeriv A (q : ℂ)) (q : ℂ) :=
      (UpperHalfPlane.hasStrictFDerivAt_smul A q).hasFDerivAt
    have hL1' : HasFDerivAt D.planePotential L1
        ((fun x : ℂ => ((A • UpperHalfPlane.ofComplex x : UpperHalfPlane) : ℂ)) (q : ℂ)) := by
      simpa only [UpperHalfPlane.ofComplex_apply] using hL1
    have first := hL1'.comp (q : ℂ) orbit
    have second := ρA.hasFDerivAt.comp (q : ℂ) hL2
    have both := first.sub second
    have zero : L1.comp (UpperHalfPlane.smulFDeriv A (q : ℂ)) - ρA.comp L2 = 0 := by
      ext d
      simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, _root_.zero_apply]
      rw [hL1d, hL2d, l3_eichlerDifferential_equivariant σ n D.cusp3 D.central_positive D.lower
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
  rw [UpperHalfPlane.coe_I, D.planePotential_I, map_zero, sub_zero] at constant
  exact sub_eq_iff_eq_add.mp constant

/-- The untwisted Hilbert-level Eichler cocycle `A ↦ P⁺(A · i)`. -/
def planeCocycle (A : BinaryRealGL) : Fin (n + 2) → σ.H := D.planePotential (basePoint A)

theorem planeCocycle_eq_l3PlaneCocycleWt (A : BinaryRealGL) :
    D.planeCocycle A = l3PlaneCocycleWt σ n D.wt D.vector.val A := rfl

/-- **The untwisted cocycle identity.** -/
theorem planeCocycle_mul (A B : BinaryRealGL) :
    D.planeCocycle (A * B) = D.planeCocycle A +
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A (D.planeCocycle B) := by
  unfold L3InputWt.planeCocycle basePoint
  rw [mul_smul]
  exact D.planePotential_affine A (B • UpperHalfPlane.I)

/-- **The untwisted cocycle vanishes on the stabilizer of `i`.** -/
theorem planeCocycle_eq_zero_of_smul_I (A : BinaryRealGL)
    (h : A • UpperHalfPlane.I = UpperHalfPlane.I) : D.planeCocycle A = 0 := by
  unfold L3InputWt.planeCocycle basePoint
  rw [h, UpperHalfPlane.coe_I]
  exact D.planePotential_I

end L3InputWt

end TernaryPeriodPolynomials.EvenLevelThree

end
