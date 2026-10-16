module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeInterface
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Symmetric.ProjectionDeriv

@[expose] public section


/-!
# Calculus of the moved vertices of the edge section

The vertices of the simplices entering the edge section of the real good-line transfer are, in
relative position, the plane points of `k(u) · lineMatrix q` for `q` on the diagonal flow and on the
axes of the lower radical. Their radical coordinates and Levi points are the symmetric projection of
the explicit matrix curves `k(u) diag(eˢ, e⁻ˢ, 1)`, `k(u) (1 + r Rᵢ)` and
`k(u) (1 + r Rᵢ) diag(eˢ, e⁻ˢ, 1)`; this file computes their derivatives at the identity. It also
records the derivative `dμ(ξ) P = ξ₀ ∂₀ P + ξ₁ ∂₁ P` of the upper binary value `μ` at `0` and the
derivative of a product whose first factor vanishes at the base point.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial Filter Topology

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

namespace EdgeExplicit

/-! ### Products with a factor vanishing at the base point -/

theorem hasDerivAt_mul_of_eq_zero {f g : ℝ → ℂ} {f' : ℂ} (hf : HasDerivAt f f' 0)
    (hf0 : f 0 = 0) (hg : ContinuousAt g 0) :
    HasDerivAt (fun s => f s * g s) (f' * g 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hf ⊢
  have product := hf.mul (hg.tendsto.mono_left nhdsWithin_le_nhds)
  refine product.congr' (eventually_nhdsWithin_of_forall fun s _ => ?_)
  rw [slope_def_module, slope_def_module, hf0, zero_mul, sub_zero, sub_zero, smul_mul_assoc,
    sub_zero]

/-- The basis expansion of a scalar test of a linear map applied to a vector. -/
theorem functional_apply_eq_sum {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*}
    [Fintype ι] (b : Module.Basis ι ℂ M) (T : M →ₗ[ℂ] ℂ) (v : M) :
    T v = ∑ j, b.coord j v * T (b j) := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]

/-- **Derivative of a moving test of a vector vanishing at the base point.** If the tests
`T s` are continuous in `s` on each vector, `v 0 = 0` and the coordinates of `v` are
differentiable at `0`, then `s ↦ T s (v s)` has derivative `T 0 (∑ c'ⱼ bⱼ)` at `0`. -/
theorem hasDerivAt_apply_of_eq_zero {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*}
    [Fintype ι] (b : Module.Basis ι ℂ M) (T : ℝ → M →ₗ[ℂ] ℂ) (v : ℝ → M) (c' : ι → ℂ)
    (hT : ∀ w, ContinuousAt (fun s => T s w) 0) (hv0 : v 0 = 0)
    (hv : ∀ j, HasDerivAt (fun s => b.coord j (v s)) (c' j) 0) :
    HasDerivAt (fun s => T s (v s)) (T 0 (∑ j, c' j • b j)) 0 := by
  have terms := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    hasDerivAt_mul_of_eq_zero (hv j) (by rw [hv0, map_zero]) (hT (b j))
  have e : (fun s => T s (v s)) = fun s => ∑ j, b.coord j (v s) * T s (b j) :=
    funext fun s => functional_apply_eq_sum b (T s) (v s)
  rw [e]
  refine terms.congr_deriv ?_
  simp only [map_sum, map_smul, smul_eq_mul]

/-! ### The derivative of the upper binary value -/

/-- The derivative `ξ ↦ ξ₀ D₀ + ξ₁ D₁` at `0` of the upper radical action, `Dᵢ = -X₂ ∂ᵢ`. -/
def upperRadicalDeriv (n : ℕ) (ξ : Fin 2 → ℝ) : Module.End ℂ (HomogeneousPoly n) :=
  (ξ 0 : ℂ) • upperRadicalGenerator n 0 + (ξ 1 : ℂ) • upperRadicalGenerator n 1

/-- **The derivative of the upper binary value** `μ` at `0` in the direction `ξ`:
`dμ(ξ) P = ξ₀ ∂₀ P + ξ₁ ∂₁ P`. -/
def muDeriv (n : ℕ) (ξ : Fin 2 → ℝ) :
    Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n :=
  -((homogeneousLastDivide n).comp ((upperRadicalDeriv (n + 1) ξ).comp
    (binaryHomogeneousLift (n + 1))))

theorem upperRadicalRep_eq_action (x : RealPlaneRadical) (Q : HomogeneousPoly n) :
    (realUpperRadicalRep n).ρ x Q =
      homogeneousAction n (-1) (planeUnipotent ((x.toAdd 0 : ℝ) : ℂ) ((x.toAdd 1 : ℝ) : ℂ)) Q := by
  change realCoefficientComponent n trivialCharacter (realPlaneRadicalMatrix x) Q = _
  rw [realCoefficientComponent_trivial]
  change homogeneousAction n (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ)
    (planeUnipotent (x.toAdd 0) (x.toAdd 1))) Q = _
  rw [map_planeUnipotent]
  rfl

/-- **The upper radical action is differentiable along curves through `0`.** -/
theorem hasDerivAt_functional_upperRadical (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (Q : HomogeneousPoly n) {Δ : ℝ → Fin 2 → ℝ} {ξ : Fin 2 → ℝ} (hΔ0 : Δ 0 = 0)
    (hΔ : HasDerivAt Δ ξ 0) :
    HasDerivAt (fun r => functional ((realUpperRadicalRep n).ρ (Multiplicative.ofAdd (Δ r)) Q))
      (functional (upperRadicalDeriv n ξ Q)) 0 := by
  have spanned := ternaryPolynomialDual_mem_span_coefficients functional
  induction spanned using Submodule.span_induction with
  | mem functional membership =>
    rcases membership with ⟨monomial, rfl⟩
    have coordinate (i : Fin 2) : HasDerivAt (fun r => ((Δ r i : ℝ) : ℂ)) ((ξ i : ℝ) : ℂ) 0 :=
      (hasDerivAt_pi.mp hΔ i).ofReal_comp
    let derivative : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, -(ξ 0 : ℂ); 0, 0, -(ξ 1 : ℂ); 0, 0, 0]
    have at_zero : planeUnipotent ((Δ 0 0 : ℝ) : ℂ) ((Δ 0 1 : ℝ) : ℂ) = 1 := by
      apply Units.ext
      funext row column
      fin_cases row <;> fin_cases column <;> simp [planeUnipotent, hΔ0]
    have determinant (r : ℝ) :
        (GeneralLinearGroup.det (planeUnipotent ((Δ r 0 : ℝ) : ℂ) ((Δ r 1 : ℝ) : ℂ))).val = 1 := by
      change Matrix.det (!![1, 0, ((Δ r 0 : ℝ) : ℂ); 0, 1, ((Δ r 1 : ℝ) : ℂ); 0, 0, 1] :
        Matrix (Fin 3) (Fin 3) ℂ) = 1
      simp [Matrix.det_fin_three]
    have entries (row column : Fin 3) : HasDerivAt (fun r =>
        (planeUnipotent ((Δ r 0 : ℝ) : ℂ) ((Δ r 1 : ℝ) : ℂ))⁻¹.val row column)
        (derivative row column) 0 := by
      change HasDerivAt (fun r => (!![1, 0, -((Δ r 0 : ℝ) : ℂ); 0, 1, -((Δ r 1 : ℝ) : ℂ);
        0, 0, 1] : Matrix (Fin 3) (Fin 3) ℂ) row column) (derivative row column) 0
      fin_cases row <;> fin_cases column <;>
        first
        | exact hasDerivAt_const 0 _
        | exact (coordinate 0).neg
        | exact (coordinate 1).neg
    have derived := ternary_homogeneousAction_coeff_hasDerivAt
      (fun r => planeUnipotent ((Δ r 0 : ℝ) : ℂ) ((Δ r 1 : ℝ) : ℂ)) derivative at_zero
      determinant entries Q monomial
    have formula : ternaryInfinitesimalSubstitution derivative Q.val =
        (upperRadicalDeriv n ξ Q).val := by
      change _ = (ξ 0 : ℂ) • ((-1 : ℂ) • (X 2 * pderiv (0 : Fin 3) Q.val)) +
        (ξ 1 : ℂ) • ((-1 : ℂ) • (X 2 * pderiv (1 : Fin 3) Q.val))
      simp [ternaryInfinitesimalSubstitution, linearForm, derivative, Fin.sum_univ_three,
        smul_eq_C_mul]
      ring
    rw [formula] at derived
    refine derived.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
    change ((realUpperRadicalRep n).ρ (Multiplicative.ofAdd (Δ r)) Q).val.coeff monomial = _
    rw [upperRadicalRep_eq_action]
    rfl
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add first second _ _ hfirst hsecond => exact hfirst.add hsecond
  | smul scalar functional _ hfunctional => exact hfunctional.const_mul scalar

/-- **The derivative of the upper binary value along curves through `0`.** -/
theorem hasDerivAt_functional_realUpperBinaryValue (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (P : Binary.HomogeneousPoly (n + 1)) {Δ : ℝ → Fin 2 → ℝ} {ξ : Fin 2 → ℝ} (hΔ0 : Δ 0 = 0)
    (hΔ : HasDerivAt Δ ξ 0) :
    HasDerivAt (fun r => functional (realUpperBinaryValue n (Multiplicative.ofAdd (Δ r)) P))
      (functional (muDeriv n ξ P)) 0 := by
  have moved := (hasDerivAt_functional_upperRadical (functional ∘ₗ homogeneousLastDivide n)
    (binaryHomogeneousLift (n + 1) P) hΔ0 hΔ).const_sub
    (functional (homogeneousLastDivide n (binaryHomogeneousLift (n + 1) P)))
  refine moved.congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
  · simp [muDeriv]
  · simp [realUpperBinaryValue]

/-! ### The vertices of the moved simplices -/

theorem lineMatrix_val_eq (q : LineGroup) :
    (lineMatrix q).val = !![1, 0, 0; 0, 1, 0; q.left.toAdd 0, q.left.toAdd 1, 1] *
      planeBlock (q.right : BinaryRealGL).val 1 := by
  rw [lineMatrix_apply]
  rfl

theorem lineVertex_corner (u : ℝ × ℝ) (q : LineGroup) :
    (gsOrth u * lineMatrix q).val 2 2 = 1 / gsRadius u := by
  rw [Units.val_mul, lineMatrix_val_eq, gsOrth_val]
  simp [Matrix.mul_apply, Fin.sum_univ_three, gsOrthMatrix, planeBlock]

theorem lineVertex_corner_pos (u : ℝ × ℝ) (q : LineGroup) :
    0 < (gsOrth u * lineMatrix q).val 2 2 := by
  rw [lineVertex_corner]
  exact one_div_pos.mpr (gsRadius_pos u)

/-- The radical part of a relative vertex is the symmetric radical coordinate. -/
theorem relativeVertex_left (u : ℝ × ℝ) (q : LineGroup) :
    (relativeVertex u q).left =
      Multiplicative.ofAdd (symmetricRadical (gsOrth u * lineMatrix q).val) := by
  rw [relativeVertex, ← gsPlaneVertex_radical (lineVertex_corner_pos u q)]
  rfl

/-- The Levi point of a relative vertex is the symmetric Levi point. -/
theorem basePoint_relativeVertex (u : ℝ × ℝ) (q : LineGroup) :
    basePoint (relativeVertex u q).right = symmetricPoint (gsOrth u * lineMatrix q).val := by
  rw [basePoint, relativeVertex, gsPlaneVertex_point (lineVertex_corner_pos u q)]

/-- **The relative integrand of the Eichler normal form through the symmetric projection.** -/
theorem relativeIntegrand_eichlerNormal (F : BinaryAdelicGL → ℂ → ℂ) (u : ℝ × ℝ)
    (a c : LineGroup) (h : BinaryAdelicGL) :
    relativeIntegrand (eichlerNormal n F) u a c h =
      transferScale n u • realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹
        ((realUpperRadicalRep n).ρ
          (Multiplicative.ofAdd (symmetricRadical (gsOrth u * lineMatrix a).val))
          (realUpperBinaryValue n (Multiplicative.ofAdd
              (symmetricRadical (gsOrth u * lineMatrix c).val -
                symmetricRadical (gsOrth u * lineMatrix a).val))
            (eichlerPointNormal n F (symmetricPoint (gsOrth u * lineMatrix a).val)
              (h * atInfinity (gsPlaneVertex (standardGoodLineRealArgument u)).right)))) := by
  rw [relativeIntegrand, pointCanonical_relative, relativeVertex_left, relativeVertex_left,
    eichlerNormal_eq_eichlerPointNormal, basePoint_relativeVertex, ← ofAdd_neg, ← ofAdd_add,
    neg_add_eq_sub]

/-! ### The moved vertices as matrix curves -/

/-- The matrix `diag(eˢ, e⁻ˢ, 1)`. -/
def flowMatrix (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.exp s, 0, 0; 0, Real.exp (-s), 0; 0, 0, 1]

/-- The velocity `H = diag(1, -1, 0)` of the diagonal flow. -/
def flowVelocity : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

/-- The velocity `Rᵢ = E₂ᵢ` of the lower radical axis `r ↦ r eᵢ`. -/
def axisVelocity (i : Fin 2) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 0, 0, 0; (Pi.single i 1 : Fin 2 → ℝ) 0, (Pi.single i 1 : Fin 2 → ℝ) 1, 0]

/-- The first diagonal matrix unit. -/
def unitFirst : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]

/-- The second diagonal matrix unit. -/
def unitSecond : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 1, 0; 0, 0, 0]

theorem flowMatrix_eq (s : ℝ) :
    flowMatrix s = 1 + (Real.exp s - 1) • unitFirst + (Real.exp (-s) - 1) • unitSecond := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [flowMatrix, unitFirst, unitSecond]

theorem flowMatrix_zero : flowMatrix 0 = 1 := by
  rw [flowMatrix_eq]
  simp

theorem det_flowMatrix (s : ℝ) : (flowMatrix s).det = 1 := by
  simp [flowMatrix, Matrix.det_fin_three, ← Real.exp_add]

theorem continuous_flowMatrix : Continuous flowMatrix := by
  have e : flowMatrix = fun s =>
      1 + (Real.exp s - 1) • unitFirst + (Real.exp (-s) - 1) • unitSecond :=
    funext flowMatrix_eq
  rw [e]
  fun_prop

theorem lineVertex_levi (u : ℝ × ℝ) (s : ℝ) :
    (gsOrth u * lineMatrix (lineLeviElement (diagonalFlow s))).val =
      gsOrthMatrix u * flowMatrix s := by
  rw [Units.val_mul, lineMatrix_val_eq, gsOrth_val]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [lineLeviElement, diagonalFlow, diagonalFlowMatrix_val, flowMatrix, planeBlock,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem lineVertex_radical_levi (u : ℝ × ℝ) (i : Fin 2) (r s : ℝ) :
    (gsOrth u * lineMatrix (lineRadicalElement (r • Pi.single i 1) *
        lineLeviElement (diagonalFlow s))).val =
      gsOrthMatrix u * flowMatrix s + r • (gsOrthMatrix u * axisVelocity i * flowMatrix s) := by
  rw [Units.val_mul, lineMatrix_val_eq, gsOrth_val, Matrix.mul_assoc (gsOrthMatrix u),
    ← Matrix.mul_smul, ← Matrix.mul_add]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp [lineLeviElement, lineRadicalElement, diagonalFlow, diagonalFlowMatrix_val, flowMatrix,
      planeBlock, axisVelocity, Matrix.mul_apply, Fin.sum_univ_three]

theorem lineVertex_radical (u : ℝ × ℝ) (i : Fin 2) (r : ℝ) :
    (gsOrth u * lineMatrix (lineRadicalElement (r • Pi.single i 1))).val =
      gsOrthMatrix u + r • (gsOrthMatrix u * axisVelocity i) := by
  rw [Units.val_mul, lineMatrix_val_eq, gsOrth_val, ← Matrix.mul_smul]
  rw [show gsOrthMatrix u + gsOrthMatrix u * r • axisVelocity i =
    gsOrthMatrix u * (1 + r • axisVelocity i) by rw [Matrix.mul_add, Matrix.mul_one]]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp [lineRadicalElement, planeBlock, axisVelocity, Matrix.mul_apply, Fin.sum_univ_three]

/-! ### Derivatives of the symmetric projection along the curves -/

theorem det_gsOrthMatrix_ne_zero (u : ℝ × ℝ) : (gsOrthMatrix u).det ≠ 0 := by
  have product := congrArg Matrix.det (gsOrthMatrix_transpose_mul u)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at product
  intro zero
  rw [zero, mul_zero] at product
  exact zero_ne_one product

theorem det_flowCurve_ne_zero (u : ℝ × ℝ) (s : ℝ) : (gsOrthMatrix u * flowMatrix s).det ≠ 0 := by
  rw [Matrix.det_mul, det_flowMatrix, mul_one]
  exact det_gsOrthMatrix_ne_zero u

theorem continuous_flowCurve (u : ℝ × ℝ) : Continuous fun s => gsOrthMatrix u * flowMatrix s :=
  continuous_const.matrix_mul continuous_flowMatrix

theorem hasDerivAt_flowCurve (u : ℝ × ℝ) :
    HasDerivAt (fun s => gsOrthMatrix u * flowMatrix s) (gsOrthMatrix u * flowVelocity) 0 := by
  have e : (fun s => gsOrthMatrix u * flowMatrix s) = fun s => gsOrthMatrix u +
      (Real.exp s - 1) • (gsOrthMatrix u * unitFirst) +
      (Real.exp (-s) - 1) • (gsOrthMatrix u * unitSecond) := by
    funext s
    rw [flowMatrix_eq, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      Matrix.mul_smul]
  rw [e]
  have first := ((Real.hasDerivAt_exp 0).sub_const 1).smul_const (gsOrthMatrix u * unitFirst)
  have second := ((hasDerivAt_neg (0 : ℝ)).exp.sub_const 1).smul_const
    (gsOrthMatrix u * unitSecond)
  refine ((first.const_add _).add second).congr_deriv ?_
  have velocity : flowVelocity = unitFirst - unitSecond := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [flowVelocity, unitFirst, unitSecond]
  rw [velocity, Matrix.mul_sub]
  simp [sub_eq_add_neg]

theorem flowCurve_zero (u : ℝ × ℝ) : gsOrthMatrix u * flowMatrix 0 = gsOrthMatrix u := by
  rw [flowMatrix_zero, Matrix.mul_one]

theorem hasDerivAt_symmetricRadical_flow (u : ℝ × ℝ) :
    HasDerivAt (fun s => symmetricRadical (gsOrthMatrix u * flowMatrix s))
      (radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity)) 0 :=
  (hasFDerivAt_symmetricRadical (gsOrthMatrix_transpose_mul u)).comp_hasDerivAt_of_eq 0
    (hasDerivAt_flowCurve u) (flowCurve_zero u).symm

theorem hasDerivAt_symmetricPoint_flow (u : ℝ × ℝ) :
    HasDerivAt (fun s => symmetricPoint (gsOrthMatrix u * flowMatrix s))
      (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity)) 0 :=
  (hasFDerivAt_symmetricPoint (gsOrthMatrix_transpose_mul u)).comp_hasDerivAt_of_eq 0
    (hasDerivAt_flowCurve u) (flowCurve_zero u).symm

theorem hasDerivAt_axisCurve (u : ℝ × ℝ) (i : Fin 2) :
    HasDerivAt (fun r : ℝ => gsOrthMatrix u + r • (gsOrthMatrix u * axisVelocity i))
      (gsOrthMatrix u * axisVelocity i) 0 := by
  refine (((hasDerivAt_id' (0 : ℝ)).smul_const (gsOrthMatrix u * axisVelocity i)).const_add
    (gsOrthMatrix u)).congr_deriv ?_
  rw [one_smul]

theorem axisCurve_zero (u : ℝ × ℝ) (i : Fin 2) :
    gsOrthMatrix u + (0 : ℝ) • (gsOrthMatrix u * axisVelocity i) = gsOrthMatrix u := by
  rw [zero_smul, add_zero]

theorem hasDerivAt_symmetricRadical_axis (u : ℝ × ℝ) (i : Fin 2) :
    HasDerivAt
      (fun r : ℝ => symmetricRadical (gsOrthMatrix u + r • (gsOrthMatrix u * axisVelocity i)))
      (radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i)) 0 :=
  (hasFDerivAt_symmetricRadical (gsOrthMatrix_transpose_mul u)).comp_hasDerivAt_of_eq 0
    (hasDerivAt_axisCurve u i) (axisCurve_zero u i).symm

theorem hasDerivAt_symmetricPoint_axis (u : ℝ × ℝ) (i : Fin 2) :
    HasDerivAt
      (fun r : ℝ => symmetricPoint (gsOrthMatrix u + r • (gsOrthMatrix u * axisVelocity i)))
      (pointDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i)) 0 :=
  (hasFDerivAt_symmetricPoint (gsOrthMatrix_transpose_mul u)).comp_hasDerivAt_of_eq 0
    (hasDerivAt_axisCurve u i) (axisCurve_zero u i).symm

theorem continuous_axisCurve (u : ℝ × ℝ) (i : Fin 2) :
    Continuous fun r : ℝ => gsOrthMatrix u + r • (gsOrthMatrix u * axisVelocity i) := by
  fun_prop

/-- The radical coordinate of the moved vertex `k(u) (1 + r Rᵢ) diag(eˢ, e⁻ˢ, 1)`, as a function
of `(s, r)`. -/
def movedRadical (u : ℝ × ℝ) (i : Fin 2) (p : ℝ × ℝ) : Fin 2 → ℝ :=
  symmetricRadical (gsOrthMatrix u * flowMatrix p.1 +
    p.2 • (gsOrthMatrix u * axisVelocity i * flowMatrix p.1))

theorem movedMatrix_eq (u : ℝ × ℝ) (i : Fin 2) (p : ℝ × ℝ) :
    gsOrthMatrix u * flowMatrix p.1 + p.2 • (gsOrthMatrix u * axisVelocity i * flowMatrix p.1) =
      gsOrthMatrix u + (Real.exp p.1 - 1) • (gsOrthMatrix u * unitFirst) +
        (Real.exp (-p.1) - 1) • (gsOrthMatrix u * unitSecond) +
        p.2 • (gsOrthMatrix u * axisVelocity i + (Real.exp p.1 - 1) •
          (gsOrthMatrix u * axisVelocity i * unitFirst) + (Real.exp (-p.1) - 1) •
          (gsOrthMatrix u * axisVelocity i * unitSecond)) := by
  rw [flowMatrix_eq]
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]

theorem contDiff_movedMatrix (u : ℝ × ℝ) (i : Fin 2) :
    ContDiff ℝ 1 fun p : ℝ × ℝ => gsOrthMatrix u * flowMatrix p.1 +
      p.2 • (gsOrthMatrix u * axisVelocity i * flowMatrix p.1) := by
  have e := funext (movedMatrix_eq u i)
  rw [e]
  fun_prop

theorem det_movedMatrix_ne_zero (u : ℝ × ℝ) (i : Fin 2) (p : ℝ × ℝ) :
    (gsOrthMatrix u * flowMatrix p.1 +
      p.2 • (gsOrthMatrix u * axisVelocity i * flowMatrix p.1)).det ≠ 0 := by
  rw [← lineVertex_radical_levi]
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _) |>.ne_zero

theorem contDiffAt_movedRadical (u : ℝ × ℝ) (i : Fin 2) (p : ℝ × ℝ) :
    ContDiffAt ℝ 1 (movedRadical u i) p :=
  (contDiffAt_symmetricRadical_of 1 (det_movedMatrix_ne_zero u i p)).comp p
    (contDiff_movedMatrix u i).contDiffAt

/-- The radical velocity along the axis at the point `k(u) · diag(eˢ, e⁻ˢ, 1)`. -/
def axisRadicalVelocity (u : ℝ × ℝ) (i : Fin 2) (s : ℝ) : Fin 2 → ℝ :=
  fderiv ℝ (movedRadical u i) (s, 0) (0, 1)

theorem hasDerivAt_movedRadical (u : ℝ × ℝ) (i : Fin 2) (s : ℝ) :
    HasDerivAt (fun r : ℝ => movedRadical u i (s, r)) (axisRadicalVelocity u i s) 0 := by
  have differentiable :=
    ((contDiffAt_movedRadical u i (s, 0)).differentiableAt (by norm_num)).hasFDerivAt
  exact differentiable.comp_hasDerivAt_of_eq 0 ((hasDerivAt_const 0 s).prodMk
    (hasDerivAt_id' 0)) rfl

theorem continuousAt_axisRadicalVelocity (u : ℝ × ℝ) (i : Fin 2) :
    ContinuousAt (axisRadicalVelocity u i) 0 := by
  have smooth : ContDiffAt ℝ 0 (fderiv ℝ (movedRadical u i)) ((0 : ℝ), (0 : ℝ)) :=
    (contDiffAt_movedRadical u i (0, 0)).fderiv_right (by norm_num)
  have path : ContinuousAt (fun s : ℝ => (s, (0 : ℝ))) 0 :=
    (continuous_id.prodMk continuous_const).continuousAt
  exact (ContinuousAt.comp (f := fun s : ℝ => (s, (0 : ℝ))) smooth.continuousAt path).clm_apply
    continuousAt_const

theorem movedRadical_axis (u : ℝ × ℝ) (i : Fin 2) (r : ℝ) :
    movedRadical u i (0, r) =
      symmetricRadical (gsOrthMatrix u + r • (gsOrthMatrix u * axisVelocity i)) := by
  rw [movedRadical, flowMatrix_zero, Matrix.mul_one, Matrix.mul_one]

theorem axisRadicalVelocity_zero (u : ℝ × ℝ) (i : Fin 2) :
    axisRadicalVelocity u i 0 =
      radicalDeriv (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity i) := by
  have axis := hasDerivAt_symmetricRadical_axis u i
  simp only [← movedRadical_axis] at axis
  exact (hasDerivAt_movedRadical u i 0).unique axis

theorem continuous_movedRadical_right (u : ℝ × ℝ) (i : Fin 2) (s : ℝ) :
    Continuous fun r : ℝ => movedRadical u i (s, r) :=
  continuous_iff_continuousAt.mpr fun r =>
    ((contDiffAt_movedRadical u i (s, r)).continuousAt).comp
      (continuous_const.prodMk continuous_id).continuousAt

end EdgeExplicit

end TernaryPeriodPolynomials.AnalyticClasses
