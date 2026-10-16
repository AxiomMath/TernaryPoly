module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeExplicitCalculus

@[expose] public section


/-!
# The mixed derivative of the edge section of the Eichler normal form

For the pointwise Eichler normal form `N = eichlerNormal n F`, the mixed derivative
`∂ₛ ∂ᵣ` at `(0, 0)` of the edge section is the scalar test of the explicit vector
`TS(u) · k⁻¹ ⋆ (dμ(ξ(Rᵢ)) N'(H) - dμ(ξ(H)) N'(Rᵢ))`, where `k = k(u)` is the orthogonal Iwasawa
factor of the good-line argument, `H = diag(1, -1, 0)` and `Rᵢ = E₂ᵢ` are the velocities of the
diagonal flow and of the lower radical axis, `ξ` and `ż` are the derivatives of the radical
coordinate and of the Levi point at `k`, `N'(W)` is the derivative of the pointwise normal form at
`i` in the direction `ż(W)`, and `dμ(ξ)` is the derivative at `0` of the upper binary value `μ`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial Filter Topology

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

namespace EdgeExplicit

/-! ### Continuity of moving tests -/

theorem continuous_realPlaneRadicalMatrix {X : Type} [TopologicalSpace X] {e : X → Fin 2 → ℝ}
    (he : Continuous e) :
    Continuous fun x => realPlaneRadicalMatrix (Multiplicative.ofAdd (e x)) := by
  have := (EdgeControl.planeContinuous_inlRadical (e := fun x => Multiplicative.ofAdd (e x))
    he).matrix
  simpa only [realPlaneMatrix_inl] using this

theorem continuous_functional_upperRadical {X : Type} [TopologicalSpace X] {e : X → Fin 2 → ℝ}
    (he : Continuous e) (Q : HomogeneousPoly n) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Continuous fun x => functional ((realUpperRadicalRep n).ρ (Multiplicative.ofAdd (e x)) Q) :=
  realCoefficientComponent_functional_continuous _ (continuous_realPlaneRadicalMatrix he) Q
    functional

theorem continuous_functional_upperRadical_binaryValue {X : Type} [TopologicalSpace X]
    {e₁ e₂ : X → Fin 2 → ℝ} (he₁ : Continuous e₁) (he₂ : Continuous e₂)
    (P : Binary.HomogeneousPoly (n + 1)) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Continuous fun x => functional ((realUpperRadicalRep n).ρ (Multiplicative.ofAdd (e₁ x))
      (realUpperBinaryValue n (Multiplicative.ofAdd (e₂ x)) P)) := by
  have e : (fun x => functional ((realUpperRadicalRep n).ρ (Multiplicative.ofAdd (e₁ x))
      (realUpperBinaryValue n (Multiplicative.ofAdd (e₂ x)) P))) = fun x =>
        ∑ j, (EdgeControl.homogeneousBasis n).coord j
            (realUpperBinaryValue n (Multiplicative.ofAdd (e₂ x)) P) *
          (functional ∘ₗ (realUpperRadicalRep n).ρ (Multiplicative.ofAdd (e₁ x)))
            (EdgeControl.homogeneousBasis n j) :=
    funext fun x => functional_apply_eq_sum (EdgeControl.homogeneousBasis n)
      (functional ∘ₗ (realUpperRadicalRep n).ρ (Multiplicative.ofAdd (e₁ x))) _
  rw [e]
  refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ ?_
  · exact EdgeControl.realUpperBinaryValue_functional_continuous
      (e := fun x => Multiplicative.ofAdd (e₂ x)) he₂ P _
  · exact continuous_functional_upperRadical he₁ _ functional

theorem muDeriv_eq_sum (ξ : Fin 2 → ℝ) (P : Binary.HomogeneousPoly (n + 1)) :
    muDeriv n ξ P = (ξ 0 : ℂ) • muDeriv n (Pi.single 0 1) P +
      (ξ 1 : ℂ) • muDeriv n (Pi.single 1 1) P := by
  simp only [muDeriv, LinearMap.neg_apply, LinearMap.comp_apply, upperRadicalDeriv,
    LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, neg_add]
  simp only [Pi.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne,
    one_ne_zero, Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, neg_zero, add_zero,
    zero_add, smul_neg]

theorem continuousAt_functional_muDeriv {e : ℝ → Fin 2 → ℝ} {ξ : ℝ → Fin 2 → ℝ}
    (he : Continuous e) (hξ : ContinuousAt ξ 0) (P : Binary.HomogeneousPoly (n + 1))
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ContinuousAt (fun s => functional ((realUpperRadicalRep n).ρ (Multiplicative.ofAdd (e s))
      (muDeriv n (ξ s) P))) 0 := by
  simp only [fun s => muDeriv_eq_sum (n := n) (ξ s) P, map_add, map_smul, smul_eq_mul]
  have coordinate (i : Fin 2) : ContinuousAt (fun s => ((ξ s i : ℝ) : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt.comp ((continuous_apply i).continuousAt.comp hξ)
  exact ((coordinate 0).mul (continuous_functional_upperRadical he _ functional).continuousAt).add
    ((coordinate 1).mul (continuous_functional_upperRadical he _ functional).continuousAt)

/-! ### The mixed derivative of the edge section -/

/-- The adelic point `h · B(u)` at which the transported normal form is evaluated. -/
def movedPoint (u : ℝ × ℝ) (h : BinaryAdelicGL) : BinaryAdelicGL :=
  h * atInfinity (gsPlaneVertex (standardGoodLineRealArgument u)).right

/-- The test `ℓ ∘ (TS(u) • k(u)⁻¹ ⋆)` of the transferred integrand. -/
def movedTest (u : ℝ × ℝ) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    HomogeneousPoly n →ₗ[ℂ] ℂ :=
  functional ∘ₗ (transferScale n u • realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹)

/-- The vertex matrix `k(u) (1 + r Rᵢ)` of the lower radical axis. -/
def axisCurve (u : ℝ × ℝ) (i : Fin 2) (r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  gsOrthMatrix u + r • (gsOrthMatrix u * axisVelocity i)

/-- The derivative at `i` of the pointwise normal form in the direction `dw`, as a vector. -/
def normalDerivVector (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) (dw : ℂ) :
    Binary.HomogeneousPoly (n + 1) :=
  ∑ j, eichlerPointNormalDeriv n F Complex.I h j dw • binaryWeightBasis (n + 1) j

/-- **The mixed derivative vector**
`TS(u) • k⁻¹ ⋆ (dμ(ξ(Rᵢ)) N'(H) - dμ(ξ(H)) N'(Rᵢ))` of the edge section. -/
def edgeMixedVector (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (u : ℝ × ℝ) (i : Fin 2)
    (h : BinaryAdelicGL) : HomogeneousPoly n :=
  (transferScale n u • realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹)
    (muDeriv n (radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i))
        (normalDerivVector n F (movedPoint u h)
          (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity))) -
      muDeriv n (radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity))
        (normalDerivVector n F (movedPoint u h)
          (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i))))

theorem eichlerPointNormal_at_I (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) :
    eichlerPointNormal n F Complex.I h = 0 := by
  rw [eichlerPointNormal, binaryComplexReflection_basepoint, eichlerPeriod_I_eq_zero, map_zero]
  simp

theorem symmetricPoint_gsOrthMatrix (u : ℝ × ℝ) : symmetricPoint (gsOrthMatrix u) = Complex.I :=
  symmetricPoint_orthogonal (gsOrthMatrix_transpose_mul u)

theorem symmetricRadical_gsOrthMatrix (u : ℝ × ℝ) : symmetricRadical (gsOrthMatrix u) = 0 :=
  symmetricRadical_orthogonal (gsOrthMatrix_transpose_mul u)

theorem upperRadical_ofAdd_zero (Q : HomogeneousPoly n) :
    (realUpperRadicalRep n).ρ (Multiplicative.ofAdd (0 : Fin 2 → ℝ)) Q = Q := by
  rw [ofAdd_zero, map_one, Module.End.one_apply]

theorem edgeSection_eichlerNormal (F : BinaryAdelicGL → ℂ → ℂ) (u : ℝ × ℝ) (i : Fin 2)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (s r : ℝ) :
    edgeSection (eichlerNormal n F) u i h functional s r =
      movedTest u functional ((realUpperRadicalRep n).ρ
          (Multiplicative.ofAdd (symmetricRadical (gsOrthMatrix u * flowMatrix s)))
        (realUpperBinaryValue n (Multiplicative.ofAdd
            (movedRadical u i (s, r) - symmetricRadical (gsOrthMatrix u * flowMatrix s)))
          (eichlerPointNormal n F (symmetricPoint (gsOrthMatrix u * flowMatrix s))
            (movedPoint u h)))) -
      movedTest u functional ((realUpperRadicalRep n).ρ
          (Multiplicative.ofAdd (symmetricRadical (axisCurve u i r)))
        (realUpperBinaryValue n (Multiplicative.ofAdd
            (movedRadical u i (s, r) - symmetricRadical (axisCurve u i r)))
          (eichlerPointNormal n F (symmetricPoint (axisCurve u i r)) (movedPoint u h)))) := by
  rw [edgeSection, relativeIntegrand_eichlerNormal, relativeIntegrand_eichlerNormal,
    lineVertex_levi, lineVertex_radical_levi, lineVertex_radical]
  rfl

theorem continuous_symmetricRadical_axis (u : ℝ × ℝ) (i : Fin 2) :
    Continuous fun r => symmetricRadical (axisCurve u i r) := by
  refine continuous_iff_continuousAt.mpr fun r => ?_
  have invertible : (axisCurve u i r).det ≠ 0 := by
    rw [axisCurve, ← lineVertex_radical]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _) |>.ne_zero
  exact ((contDiffAt_symmetricRadical_of 0 invertible).continuousAt).comp
    (continuous_axisCurve u i).continuousAt

theorem continuous_symmetricRadical_flow (u : ℝ × ℝ) :
    Continuous fun s => symmetricRadical (gsOrthMatrix u * flowMatrix s) :=
  continuous_iff_continuousAt.mpr fun s =>
    ContinuousAt.comp (f := fun s => gsOrthMatrix u * flowMatrix s)
      ((contDiffAt_symmetricRadical_of 0 (det_flowCurve_ne_zero u s)).continuousAt)
      (continuous_flowCurve u).continuousAt

variable (F : BinaryAdelicGL → ℂ → ℂ)
  (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})

include holomorphic in
theorem hasDerivAt_coord_normal_flow (u : ℝ × ℝ) (h : BinaryAdelicGL) (j : Fin (n + 2)) :
    HasDerivAt (fun s => (binaryWeightBasis (n + 1)).coord j
        (eichlerPointNormal n F (symmetricPoint (gsOrthMatrix u * flowMatrix s)) h))
      (eichlerPointNormalDeriv n F Complex.I h j
        (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity))) 0 :=
  (hasFDerivAt_coord_eichlerPointNormal F holomorphic (z := Complex.I) (by simp) h
    j).comp_hasDerivAt_of_eq 0 (hasDerivAt_symmetricPoint_flow u)
    (by rw [flowCurve_zero, symmetricPoint_gsOrthMatrix])

include holomorphic in
theorem hasDerivAt_coord_normal_axis (u : ℝ × ℝ) (i : Fin 2) (h : BinaryAdelicGL)
    (j : Fin (n + 2)) :
    HasDerivAt (fun r => (binaryWeightBasis (n + 1)).coord j
        (eichlerPointNormal n F (symmetricPoint (axisCurve u i r)) h))
      (eichlerPointNormalDeriv n F Complex.I h j
        (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i))) 0 :=
  (hasFDerivAt_coord_eichlerPointNormal F holomorphic (z := Complex.I) (by simp) h
    j).comp_hasDerivAt_of_eq 0 (hasDerivAt_symmetricPoint_axis u i)
    (by rw [show axisCurve u i 0 = gsOrthMatrix u from axisCurve_zero u i,
      symmetricPoint_gsOrthMatrix])

/-- The radical derivative of the first edge term, for fixed `s`. -/
theorem hasDerivAt_edgeFirst (u : ℝ × ℝ) (i : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (s : ℝ) :
    HasDerivAt (fun r => movedTest u functional ((realUpperRadicalRep n).ρ
          (Multiplicative.ofAdd (symmetricRadical (gsOrthMatrix u * flowMatrix s)))
        (realUpperBinaryValue n (Multiplicative.ofAdd
            (movedRadical u i (s, r) - symmetricRadical (gsOrthMatrix u * flowMatrix s)))
          (eichlerPointNormal n F (symmetricPoint (gsOrthMatrix u * flowMatrix s))
            (movedPoint u h)))))
      (movedTest u functional ((realUpperRadicalRep n).ρ
          (Multiplicative.ofAdd (symmetricRadical (gsOrthMatrix u * flowMatrix s)))
        (muDeriv n (axisRadicalVelocity u i s)
          (eichlerPointNormal n F (symmetricPoint (gsOrthMatrix u * flowMatrix s))
            (movedPoint u h))))) 0 := by
  have base : movedRadical u i (s, 0) - symmetricRadical (gsOrthMatrix u * flowMatrix s) = 0 := by
    rw [movedRadical, zero_smul, add_zero, sub_self]
  have derived := hasDerivAt_functional_realUpperBinaryValue (movedTest u functional ∘ₗ
    (realUpperRadicalRep n).ρ (Multiplicative.ofAdd
      (symmetricRadical (gsOrthMatrix u * flowMatrix s))))
    (eichlerPointNormal n F (symmetricPoint (gsOrthMatrix u * flowMatrix s)) (movedPoint u h))
    base ((hasDerivAt_movedRadical u i s).sub_const _)
  simp only [LinearMap.comp_apply] at derived
  exact derived

include holomorphic in
/-- The flow derivative of the radical derivative of the first edge term. -/
theorem hasDerivAt_edgeFirst_flow (u : ℝ × ℝ) (i : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    HasDerivAt (fun s => movedTest u functional ((realUpperRadicalRep n).ρ
          (Multiplicative.ofAdd (symmetricRadical (gsOrthMatrix u * flowMatrix s)))
        (muDeriv n (axisRadicalVelocity u i s)
          (eichlerPointNormal n F (symmetricPoint (gsOrthMatrix u * flowMatrix s))
            (movedPoint u h)))))
      (movedTest u functional
        (muDeriv n (radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i))
          (normalDerivVector n F (movedPoint u h)
            (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity))))) 0 := by
  have derived := hasDerivAt_apply_of_eq_zero (binaryWeightBasis (n + 1))
    (fun s => (movedTest u functional ∘ₗ (realUpperRadicalRep n).ρ (Multiplicative.ofAdd
      (symmetricRadical (gsOrthMatrix u * flowMatrix s)))) ∘ₗ muDeriv n (axisRadicalVelocity u i s))
    (fun s => eichlerPointNormal n F (symmetricPoint (gsOrthMatrix u * flowMatrix s))
      (movedPoint u h))
    (fun j => eichlerPointNormalDeriv n F Complex.I (movedPoint u h) j
      (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity)))
    (fun w => by
      simp only [LinearMap.comp_apply]
      exact continuousAt_functional_muDeriv (continuous_symmetricRadical_flow u)
        (continuousAt_axisRadicalVelocity u i) w _)
    (by
      change eichlerPointNormal n F (symmetricPoint (gsOrthMatrix u * flowMatrix 0))
        (movedPoint u h) = 0
      rw [flowCurve_zero, symmetricPoint_gsOrthMatrix, eichlerPointNormal_at_I])
    (fun j => hasDerivAt_coord_normal_flow F holomorphic u (movedPoint u h) j)
  simp only [LinearMap.comp_apply, flowCurve_zero, symmetricRadical_gsOrthMatrix,
    axisRadicalVelocity_zero, ofAdd_zero, map_one, Module.End.one_apply] at derived
  exact derived

include holomorphic in
/-- The radical derivative of the second edge term, for fixed `s`. -/
theorem hasDerivAt_edgeSecond (u : ℝ × ℝ) (i : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (s : ℝ) :
    HasDerivAt (fun r => movedTest u functional ((realUpperRadicalRep n).ρ
          (Multiplicative.ofAdd (symmetricRadical (axisCurve u i r)))
        (realUpperBinaryValue n (Multiplicative.ofAdd
            (movedRadical u i (s, r) - symmetricRadical (axisCurve u i r)))
          (eichlerPointNormal n F (symmetricPoint (axisCurve u i r)) (movedPoint u h)))))
      (movedTest u functional (realUpperBinaryValue n (Multiplicative.ofAdd
          (symmetricRadical (gsOrthMatrix u * flowMatrix s)))
        (normalDerivVector n F (movedPoint u h)
          (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i))))) 0 := by
  have derived := hasDerivAt_apply_of_eq_zero (binaryWeightBasis (n + 1))
    (fun r => (movedTest u functional ∘ₗ (realUpperRadicalRep n).ρ (Multiplicative.ofAdd
      (symmetricRadical (axisCurve u i r)))) ∘ₗ realUpperBinaryValue n (Multiplicative.ofAdd
        (movedRadical u i (s, r) - symmetricRadical (axisCurve u i r))))
    (fun r => eichlerPointNormal n F (symmetricPoint (axisCurve u i r)) (movedPoint u h))
    (fun j => eichlerPointNormalDeriv n F Complex.I (movedPoint u h) j
      (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i)))
    (fun w => by
      simp only [LinearMap.comp_apply]
      exact (continuous_functional_upperRadical_binaryValue
        (continuous_symmetricRadical_axis u i)
        ((continuous_movedRadical_right u i s).sub (continuous_symmetricRadical_axis u i)) w
        (movedTest u functional)).continuousAt)
    (by
      change eichlerPointNormal n F (symmetricPoint (axisCurve u i 0)) (movedPoint u h) = 0
      rw [show axisCurve u i 0 = gsOrthMatrix u from axisCurve_zero u i,
        symmetricPoint_gsOrthMatrix, eichlerPointNormal_at_I])
    (fun j => hasDerivAt_coord_normal_axis F holomorphic u i (movedPoint u h) j)
  have point : axisCurve u i 0 = gsOrthMatrix u := axisCurve_zero u i
  have moved : movedRadical u i (s, 0) = symmetricRadical (gsOrthMatrix u * flowMatrix s) := by
    rw [movedRadical, zero_smul, add_zero]
  simp only [LinearMap.comp_apply, point, symmetricRadical_gsOrthMatrix, moved, sub_zero]
    at derived
  rw [upperRadical_ofAdd_zero] at derived
  exact derived

/-- The flow derivative of the radical derivative of the second edge term. -/
theorem hasDerivAt_edgeSecond_flow (u : ℝ × ℝ) (i : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    HasDerivAt (fun s => movedTest u functional (realUpperBinaryValue n (Multiplicative.ofAdd
          (symmetricRadical (gsOrthMatrix u * flowMatrix s)))
        (normalDerivVector n F (movedPoint u h)
          (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i)))))
      (movedTest u functional
        (muDeriv n (radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity))
          (normalDerivVector n F (movedPoint u h)
            (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i))))) 0 :=
  hasDerivAt_functional_realUpperBinaryValue (movedTest u functional) _
    (by rw [flowCurve_zero, symmetricRadical_gsOrthMatrix]) (hasDerivAt_symmetricRadical_flow u)

include holomorphic in
/-- **The mixed derivative of the edge section of the Eichler normal form** is the scalar test of
`edgeMixedVector`. -/
theorem edgeMixed_eichlerNormal (u : ℝ × ℝ) (i : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    edgeMixed (eichlerNormal n F) u i h functional = functional (edgeMixedVector n F u i h) := by
  have inner : (fun s => deriv (fun r => edgeSection (eichlerNormal n F) u i h functional s r) 0) =
      fun s => movedTest u functional ((realUpperRadicalRep n).ρ
          (Multiplicative.ofAdd (symmetricRadical (gsOrthMatrix u * flowMatrix s)))
        (muDeriv n (axisRadicalVelocity u i s)
          (eichlerPointNormal n F (symmetricPoint (gsOrthMatrix u * flowMatrix s))
            (movedPoint u h)))) -
        movedTest u functional (realUpperBinaryValue n (Multiplicative.ofAdd
          (symmetricRadical (gsOrthMatrix u * flowMatrix s)))
        (normalDerivVector n F (movedPoint u h)
          (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i)))) := by
    funext s
    simp only [edgeSection_eichlerNormal]
    exact ((hasDerivAt_edgeFirst F u i h functional s).sub
      (hasDerivAt_edgeSecond F holomorphic u i h functional s)).deriv
  rw [edgeMixed, inner]
  refine ((hasDerivAt_edgeFirst_flow F holomorphic u i h functional).sub
    (hasDerivAt_edgeSecond_flow F u i h functional)).deriv.trans ?_
  rw [← map_sub]
  rfl

end EdgeExplicit

end TernaryPeriodPolynomials.AnalyticClasses
