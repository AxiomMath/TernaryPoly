module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeAnalyticRegular

@[expose] public section


/-!
# The derivative of the derivative edge along the diagonal flow

For a scalar form `F` with `EichlerData n F` and `n ≥ 5`, let `t` be the inhomogeneous real
good-line transfer of the pointwise Eichler normal form. Along the axis `r eᵢ` of the radical, the
radical edge function of `t` at the diagonal flow `a(s)` is the integral over `u` of the edge
section, so the edge component of `t` at `a(s)` is the integral of `∂ᵣ` of the edge section at
`r = 0`. In the first term of the edge section `r` enters only the radical difference, and in the
second term `r` enters the first vertex only through the radical element `e^{r eᵢ}`. Hence the
`r`-derivative is a finite combination of coordinates of the normal form along the flow, of first
derivatives of the normal form at a point that does not depend on `s`, and of smooth functions of
`(k(u), s)`. It is therefore uniformly Lipschitz in `s`, and the edge component along the flow is
differentiable at `s = 0`, with derivative the integrated mixed derivative of the edge section.
The same holds for the weight-basis coordinates of the derivative edge.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl

variable {n : ℕ} {F : BinaryAdelicGL → ℂ → ℂ}

/-! ### The radical edge function as an integral of the edge section -/

theorem lineLevi_mul_conj_radical (m : unimodularLevi) (Y : Fin 2 → ℝ) :
    lineLeviElement m * lineRadicalElement (Matrix.vecMul Y (m : BinaryRealGL).val) =
      lineRadicalElement Y * lineLeviElement m := by
  rw [← lineLevi_conj_radical]
  group

theorem radicalEdge_eq_integral (large : 5 ≤ n) (hF : EichlerData n F) (m : unimodularLevi)
    (Y : Fin 2 → ℝ) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    radicalEdge (lineTransferCochain (eichlerNormal n F)) m Y (h, functional) =
      ∫ u, (functional (relativeIntegrand (eichlerNormal n F) u (lineLeviElement m)
          (lineRadicalElement Y * lineLeviElement m) h) -
        functional (relativeIntegrand (eichlerNormal n F) u (lineRadicalElement Y)
          (lineRadicalElement Y * lineLeviElement m) h)) ∂((volume : Measure ℝ).prod volume) := by
  rw [radicalEdge_eq]
  change lineTransferCochain _ _ _ (h, functional) - lineTransferCochain _ _ _ (h, functional) = _
  rw [lineTransferCochain_apply, lineTransferCochain_apply, lineLevi_mul_conj_radical,
    integral_sub (integrable_functional_relativeIntegrand large hF _ _ h functional)
      (integrable_functional_relativeIntegrand large hF _ _ h functional)]

/-- The edge component is the derivative of the radical edge function along the axis. -/
theorem edgeComponent_eq_deriv {t : LineGroup → LineGroup → LineValues n}
    (regular : EdgeRegular t) (m : unimodularLevi) (i : Fin 2)
    (p : BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ)) :
    edgeComponent t m i p = deriv (fun r : ℝ => radicalEdge t m (r • Pi.single i 1) p) 0 := by
  have outer := (regular.edge_differentiable m p).hasFDerivAt
  have line : HasDerivAt (fun r : ℝ => r • (Pi.single i 1 : Fin 2 → ℝ)) (Pi.single i 1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin 2 → ℝ)
  exact (outer.comp_hasDerivAt_of_eq (0 : ℝ) line (by simp)).deriv.symm

/-! ### Differentiation in the radical variable -/

/-- The regular part of the edge section. -/
def sectionRegular (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (i : Fin 2) (u : ℝ × ℝ) (s r : ℝ) : ℂ :=
  transferRegular n F h functional (lineLeviElement (diagonalFlow s))
      (lineRadicalElement (r • Pi.single i 1) * lineLeviElement (diagonalFlow s)) u -
    transferRegular n F h functional (lineRadicalElement (r • Pi.single i 1))
      (lineRadicalElement (r • Pi.single i 1) * lineLeviElement (diagonalFlow s)) u

theorem edgeSection_eq (u : ℝ × ℝ) (i : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (s r : ℝ) :
    edgeSection (eichlerNormal n F) u i h functional s r =
      transferScale n u * sectionRegular n F h functional i u s r := by
  unfold edgeSection sectionRegular
  rw [functional_relativeIntegrand, functional_relativeIntegrand, mul_sub]

theorem continuous_edgeSection (hF : EichlerData n F) (i : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (s r : ℝ) :
    Continuous (fun u => edgeSection (eichlerNormal n F) u i h functional s r) :=
  (continuous_functional_relativeIntegrand hF _ _ h functional).sub
    (continuous_functional_relativeIntegrand hF _ _ h functional)

theorem hasDerivAt_integral_edgeSection (large : 5 ≤ n) (hF : EichlerData n F) (i : Fin 2)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (s : ℝ) :
    HasDerivAt (fun r => ∫ u, edgeSection (eichlerNormal n F) u i h functional s r
        ∂((volume : Measure ℝ).prod volume))
      (∫ u, deriv (fun r => edgeSection (eichlerNormal n F) u i h functional s r) 0
        ∂((volume : Measure ℝ).prod volume)) 0 := by
  have first : SmoothLineFamily (fun _ : ℝ => lineLeviElement (diagonalFlow s)) :=
    SmoothLineFamily.const _
  have second : SmoothLineFamily
      (fun r : ℝ => lineRadicalElement (r • Pi.single i 1) * lineLeviElement (diagonalFlow s)) :=
    (smoothLineFamily_axis i).mul (SmoothLineFamily.const _)
  have uniform := (uniformLipOn_transferRegular hF first second (isCompact_closedBall (0 : ℝ) 1)
    (convex_closedBall 0 1) h functional).sub (uniformLipOn_transferRegular hF
      (smoothLineFamily_axis i) second (isCompact_closedBall (0 : ℝ) 1) (convex_closedBall 0 1) h
        functional)
  refine hasDerivAt_integral_of_uniformLipOn (B := Metric.closedBall 0 1) (T := transferScale n)
    (f := fun u r => sectionRegular n F h functional i u s r)
    (Metric.closedBall_mem_nhds 0 one_pos) (integrable_norm_transferScale large)
    (fun r _ u => edgeSection_eq u i h functional s r) uniform
    (fun r => (continuous_edgeSection hF i h functional s r).aestronglyMeasurable) fun u => ?_
  simp only [edgeSection_eq]
  exact ((differentiableAt_transferRegular hF first second h functional u 0).sub
    (differentiableAt_transferRegular hF (smoothLineFamily_axis i) second h functional u
      0)).const_mul _

/-! ### The explicit radical derivative of the edge section -/

/-- The diagonal flow as a family over `(s, r)`. -/
def levFamily (x : ℝ × ℝ) : LineGroup := lineLeviElement (diagonalFlow x.1)

/-- The radical axis as a family over `(s, r)`. -/
def axisFamily (i : Fin 2) (x : ℝ × ℝ) : LineGroup := lineRadicalElement (x.2 • Pi.single i 1)

/-- The product `e^{r eᵢ} a(s)` as a family over `(s, r)`. -/
def sectionFamily (i : Fin 2) (x : ℝ × ℝ) : LineGroup := axisFamily i x * levFamily x

theorem smoothLineFamily_levFamily : SmoothLineFamily levFamily :=
  smoothLineFamily_diagonal.comp contDiff_fst

theorem smoothLineFamily_axisFamily (i : Fin 2) : SmoothLineFamily (axisFamily i) :=
  (smoothLineFamily_axis i).comp contDiff_snd

theorem smoothLineFamily_sectionFamily (i : Fin 2) : SmoothLineFamily (sectionFamily i) :=
  (smoothLineFamily_axisFamily i).mul smoothLineFamily_levFamily

/-- The derivative at `r = 0` of a function of `(k, (s, r))`, as a function of `(k, s)`. -/
def gammaOf (R : Matrix (Fin 3) (Fin 3) ℝ × (ℝ × ℝ) → ℂ) (x : Matrix (Fin 3) (Fin 3) ℝ × ℝ) : ℂ :=
  deriv (fun r => R (x.1, (x.2, r))) 0

theorem contDiffAt_gammaOf {R : Matrix (Fin 3) (Fin 3) ℝ × (ℝ × ℝ) → ℂ}
    {k : Matrix (Fin 3) (Fin 3) ℝ} {s : ℝ} (hR : ContDiffAt ℝ 2 R (k, (s, 0))) :
    ContDiffAt ℝ 1 (gammaOf R) (k, s) := by
  have shuffle : ContDiff ℝ 2
      (fun y : (Matrix (Fin 3) (Fin 3) ℝ × ℝ) × ℝ => (y.1.1, (y.1.2, y.2))) :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  have joint : ContDiffAt ℝ 2
      (Function.uncurry fun (x : Matrix (Fin 3) (Fin 3) ℝ × ℝ) (r : ℝ) => R (x.1, (x.2, r)))
      ((k, s), 0) := by
    have composed := hR.comp ((k, s), (0 : ℝ)) shuffle.contDiffAt
    exact composed
  have derivative := ContDiffAt.fderiv
    (f := fun (x : Matrix (Fin 3) (Fin 3) ℝ × ℝ) (r : ℝ) => R (x.1, (x.2, r)))
    (g := fun _ => (0 : ℝ)) (x₀ := (k, s)) (m := 1) joint contDiffAt_const (by norm_num)
  have evaluated :=
    ((ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).contDiff.contDiffAt).comp (k, s) derivative
  exact evaluated

theorem contDiffAt_slice {R : Matrix (Fin 3) (Fin 3) ℝ × (ℝ × ℝ) → ℂ}
    {k : Matrix (Fin 3) (Fin 3) ℝ} {s : ℝ} (hR : ContDiffAt ℝ 2 R (k, (s, 0))) :
    ContDiffAt ℝ 1 (fun x : Matrix (Fin 3) (Fin 3) ℝ × ℝ => R (x.1, (x.2, 0))) (k, s) := by
  have slice : ContDiff ℝ 2 (fun x : Matrix (Fin 3) (Fin 3) ℝ × ℝ => (x.1, (x.2, (0 : ℝ)))) :=
    contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
  have composed := hR.comp (k, s) slice.contDiffAt
  exact composed.of_le (by norm_num)

/-- The coordinates of the normal form at the Levi points of the diagonal flow. -/
def leviCoord (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) (j : Fin (n + 2))
    (u : ℝ × ℝ) (s : ℝ) : ℂ :=
  (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F
    (movedPoint (fun s : ℝ => (lineMatrix (lineLeviElement (diagonalFlow s))).val)
      ((gsOrth u).val, s)) (movedAdelic h u))

/-- The coordinates of the normal form at the Levi points of the radical axis. -/
def axisCoord (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) (i : Fin 2)
    (j : Fin (n + 2)) (u : ℝ × ℝ) (r : ℝ) : ℂ :=
  (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F
    (movedPoint (fun r : ℝ => (lineMatrix (lineRadicalElement (r • Pi.single i 1))).val)
      ((gsOrth u).val, r)) (movedAdelic h u))

/-- The scalar tests `ℓ_u(e_m)`. -/
def testCoeff (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (u : ℝ × ℝ)
    (m : Fin (Module.finrank ℂ (HomogeneousPoly n))) : ℂ :=
  functional (realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹ (homogeneousBasis n m))

/-- The derivative at `r = 0` of the regular part of the edge section. -/
def sectionDeriv (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (i : Fin 2) (u : ℝ × ℝ) (s : ℝ) : ℂ :=
  (∑ j : Fin (n + 2), ∑ m, leviCoord n F h j u s * testCoeff functional u m *
      gammaOf (familyRadicalValue levFamily (sectionFamily i) m j) ((gsOrth u).val, s)) -
    ∑ j : Fin (n + 2), ∑ m, (deriv (axisCoord n F h i j u) 0 * testCoeff functional u m *
        familyRadicalValue (axisFamily i) (sectionFamily i) m j ((gsOrth u).val, (s, 0)) +
      axisCoord n F h i j u 0 * testCoeff functional u m *
        gammaOf (familyRadicalValue (axisFamily i) (sectionFamily i) m j) ((gsOrth u).val, s))

theorem sectionRegular_eq (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (i : Fin 2) (u : ℝ × ℝ) (s : ℝ) :
    (fun r => sectionRegular n F h functional i u s r) = fun r =>
      (∑ j : Fin (n + 2), ∑ m, leviCoord n F h j u s * testCoeff functional u m *
        familyRadicalValue levFamily (sectionFamily i) m j ((gsOrth u).val, (s, r))) -
      ∑ j : Fin (n + 2), ∑ m, axisCoord n F h i j u r * testCoeff functional u m *
        familyRadicalValue (axisFamily i) (sectionFamily i) m j ((gsOrth u).val, (s, r)) :=
  rfl

theorem hasDerivAt_familyRadicalValue_slice {a c : ℝ × ℝ → LineGroup} (ha : SmoothLineFamily a)
    (hc : SmoothLineFamily c) (m : Fin (Module.finrank ℂ (HomogeneousPoly n)))
    (j : Fin (n + 2)) (u : ℝ × ℝ) (s : ℝ) :
    HasDerivAt (fun r => familyRadicalValue (n := n) a c m j ((gsOrth u).val, (s, r)))
      (gammaOf (familyRadicalValue a c m j) ((gsOrth u).val, s)) 0 := by
  have smooth := contDiffAt_familyRadicalValue ha hc m j (gsOrth_val_mem u) (s, 0)
  have path : DifferentiableAt ℝ (fun r : ℝ => ((gsOrth u).val, (s, r))) 0 :=
    (differentiableAt_const _).prodMk ((differentiableAt_const s).prodMk differentiableAt_id)
  have composed := (smooth.differentiableAt (by norm_num)).comp (0 : ℝ) path
  exact composed.hasDerivAt

theorem hasDerivAt_sectionRegular (hF : EichlerData n F) (i : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (u : ℝ × ℝ) (s : ℝ) :
    HasDerivAt (fun r => sectionRegular n F h functional i u s r)
      (sectionDeriv n F h functional i u s) 0 := by
  have levi := hasDerivAt_familyRadicalValue_slice smoothLineFamily_levFamily
    (smoothLineFamily_sectionFamily i) (n := n) (u := u) (s := s)
  have axis := hasDerivAt_familyRadicalValue_slice (smoothLineFamily_axisFamily i)
    (smoothLineFamily_sectionFamily i) (n := n) (u := u) (s := s)
  have coordinate (j : Fin (n + 2)) : HasDerivAt (axisCoord n F h i j u)
      (deriv (axisCoord n F h i j u) 0) 0 :=
    (differentiableAt_pointCoord hF (smoothLineFamily_axis i) j (movedAdelic h u)
      (gsOrth_val_mem u) 0).hasDerivAt
  have first := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun m _ =>
      (levi m j).const_mul (leviCoord n F h j u s * testCoeff functional u m)
  have second := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun m _ =>
      ((coordinate j).mul_const (testCoeff functional u m)).mul (axis m j)
  rw [sectionRegular_eq]
  exact first.sub second

/-! ### Uniform regularity in the flow variable -/

theorem uniformLipOn_sectionDeriv (hF : EichlerData n F) (i : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    UniformLipOn (fun u s => sectionDeriv n F h functional i u s) (Metric.closedBall 0 1) := by
  have hB := isCompact_closedBall (0 : ℝ) 1
  have hconv := convex_closedBall (0 : ℝ) 1
  have coefficient (m : Fin (Module.finrank ℂ (HomogeneousPoly n))) :
      UniformLipOn (fun u (_ : ℝ) => testCoeff functional u m) (Metric.closedBall 0 1) := by
    obtain ⟨D, hD⟩ := exists_bound_orthogonal_functional functional (homogeneousBasis n m)
    exact UniformLipOn.const hD
  have gamma {a c : ℝ × ℝ → LineGroup} (ha : SmoothLineFamily a) (hc : SmoothLineFamily c)
      (m : Fin (Module.finrank ℂ (HomogeneousPoly n))) (j : Fin (n + 2)) :
      UniformLipOn (fun u s => gammaOf (familyRadicalValue a c m j) ((gsOrth u).val, s))
        (Metric.closedBall 0 1) :=
    uniformLipOn_orthogonal hB hconv fun k hk s _ =>
      contDiffAt_gammaOf (contDiffAt_familyRadicalValue ha hc m j hk (s, 0))
  have axisBound (j : Fin (n + 2)) : ∃ D : ℝ, 0 ≤ D ∧ ∀ u,
      ‖deriv (axisCoord n F h i j u) 0‖ ≤ D ∧ ‖axisCoord n F h i j u 0‖ ≤ D := by
    obtain ⟨D, hD0, hD⟩ := (uniformLipOn_pointCoord hF (smoothLineFamily_axis i) hB hconv j
      (movedAdelic h)).lipschitzOnWith
    refine ⟨D, hD0, fun u => ⟨?_, (hD u).1 0 (Metric.mem_closedBall_self zero_le_one)⟩⟩
    have := norm_deriv_le_of_lipschitzOn (Metric.closedBall_mem_nhds (0 : ℝ) one_pos) (hD u).2
    rwa [Real.coe_toNNReal _ hD0] at this
  unfold sectionDeriv
  refine UniformLipOn.sub (UniformLipOn.sum _ fun j _ => UniformLipOn.sum _ fun m _ => ?_)
    (UniformLipOn.sum _ fun j _ => UniformLipOn.sum _ fun m _ => ?_)
  · exact ((uniformLipOn_pointCoord hF smoothLineFamily_diagonal hB hconv j
      (movedAdelic h)).mul (coefficient m)).mul
        (gamma smoothLineFamily_levFamily (smoothLineFamily_sectionFamily i) m j)
  · obtain ⟨D, -, hD⟩ := axisBound j
    have slice : UniformLipOn (fun u s => familyRadicalValue (axisFamily i) (sectionFamily i) m j
        ((gsOrth u).val, (s, 0))) (Metric.closedBall 0 1) :=
      uniformLipOn_orthogonal (f := fun x => familyRadicalValue (axisFamily i) (sectionFamily i) m j
        (x.1, (x.2, 0))) hB hconv fun k hk s _ => contDiffAt_slice
          (contDiffAt_familyRadicalValue (smoothLineFamily_axisFamily i)
            (smoothLineFamily_sectionFamily i) m j hk (s, 0))
    exact (((UniformLipOn.const (fun u => (hD u).1)).mul (coefficient m)).mul slice).add
      (((UniformLipOn.const (fun u => (hD u).2)).mul (coefficient m)).mul
        (gamma (smoothLineFamily_axisFamily i) (smoothLineFamily_sectionFamily i) m j))

theorem differentiableAt_sectionDeriv (hF : EichlerData n F) (i : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (u : ℝ × ℝ) :
    DifferentiableAt ℝ (fun s => sectionDeriv n F h functional i u s) 0 := by
  have path : DifferentiableAt ℝ (fun s : ℝ => ((gsOrth u).val, s)) 0 :=
    (differentiableAt_const _).prodMk differentiableAt_id
  have gamma {a c : ℝ × ℝ → LineGroup} (ha : SmoothLineFamily a) (hc : SmoothLineFamily c)
      (m : Fin (Module.finrank ℂ (HomogeneousPoly n))) (j : Fin (n + 2)) :
      DifferentiableAt ℝ (fun s => gammaOf (familyRadicalValue a c m j) ((gsOrth u).val, s)) 0 := by
    have smooth := contDiffAt_gammaOf
      (contDiffAt_familyRadicalValue ha hc m j (gsOrth_val_mem u) ((0 : ℝ), 0))
    have composed := (smooth.differentiableAt (by norm_num)).comp (0 : ℝ) path
    exact composed
  unfold sectionDeriv
  refine DifferentiableAt.sub (DifferentiableAt.fun_sum fun j _ =>
    DifferentiableAt.fun_sum fun m _ => ?_) (DifferentiableAt.fun_sum fun j _ =>
      DifferentiableAt.fun_sum fun m _ => ?_)
  · exact ((differentiableAt_pointCoord hF smoothLineFamily_diagonal j (movedAdelic h u)
      (gsOrth_val_mem u) 0).mul (differentiableAt_const _)).mul
        (gamma smoothLineFamily_levFamily (smoothLineFamily_sectionFamily i) m j)
  · have slice := contDiffAt_slice (contDiffAt_familyRadicalValue (smoothLineFamily_axisFamily i)
      (smoothLineFamily_sectionFamily i) m j (gsOrth_val_mem u) ((0 : ℝ), 0))
    have composed := (slice.differentiableAt (by norm_num)).comp (0 : ℝ) path
    exact ((differentiableAt_const _).mul composed).add
      ((differentiableAt_const _).mul
        (gamma (smoothLineFamily_axisFamily i) (smoothLineFamily_sectionFamily i) m j))

/-! ### Differentiation in the flow variable -/

theorem deriv_edgeSection_eq (hF : EichlerData n F) (i : Fin 2) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (s : ℝ) (u : ℝ × ℝ) :
    HasDerivAt (fun r => edgeSection (eichlerNormal n F) u i h functional s r)
      (transferScale n u * sectionDeriv n F h functional i u s) 0 := by
  simp only [edgeSection_eq]
  exact (hasDerivAt_sectionRegular hF i h functional u s).const_mul _

theorem hasDerivAt_integral_sectionDerivative (large : 5 ≤ n) (hF : EichlerData n F) (i : Fin 2)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    HasDerivAt (fun s => ∫ u, deriv (fun r => edgeSection (eichlerNormal n F) u i h functional s r)
        0 ∂((volume : Measure ℝ).prod volume))
      (edgeMixedIntegral (eichlerNormal n F) i (h, functional)) 0 := by
  have equal (s : ℝ) (u : ℝ × ℝ) :
      deriv (fun r => edgeSection (eichlerNormal n F) u i h functional s r) 0 =
        transferScale n u * sectionDeriv n F h functional i u s :=
    (deriv_edgeSection_eq hF i h functional s u).deriv
  have measurable (s : ℝ) : AEStronglyMeasurable
      (fun u => deriv (fun r => edgeSection (eichlerNormal n F) u i h functional s r) 0)
      ((volume : Measure ℝ).prod volume) :=
    aestronglyMeasurable_of_hasDerivAt
      (f := fun r u => edgeSection (eichlerNormal n F) u i h functional s r) (x₀ := 0)
      (fun r => (continuous_edgeSection hF i h functional s r).aestronglyMeasurable)
      (Eventually.of_forall fun u => by
        rw [equal]
        exact deriv_edgeSection_eq hF i h functional s u)
  have result := hasDerivAt_integral_of_uniformLipOn
    (I := fun s u => deriv (fun r => edgeSection (eichlerNormal n F) u i h functional s r) 0)
    (T := transferScale n) (f := fun u s => sectionDeriv n F h functional i u s)
    (B := Metric.closedBall 0 1) (Metric.closedBall_mem_nhds 0 one_pos)
    (integrable_norm_transferScale large) (fun s _ u => equal s u)
    (uniformLipOn_sectionDeriv hF i h functional) measurable fun u => by
      simp only [equal]
      exact (differentiableAt_sectionDeriv hF i h functional u).const_mul _
  exact result

/-! ### The derivative of the derivative edge along the diagonal flow -/

theorem edgeComponent_diagonal_eq (large : 5 ≤ n) (hF : EichlerData n F) (i : Fin 2)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (s : ℝ) :
    edgeComponent (lineTransferCochain (eichlerNormal n F)) (diagonalFlow s) i (h, functional) =
      ∫ u, deriv (fun r => edgeSection (eichlerNormal n F) u i h functional s r) 0
        ∂((volume : Measure ℝ).prod volume) := by
  rw [edgeComponent_eq_deriv (edgeRegular_eichlerNormal large hF)]
  have integral : (fun r : ℝ => radicalEdge (lineTransferCochain (eichlerNormal n F))
      (diagonalFlow s) (r • Pi.single i 1) (h, functional)) =
      fun r => ∫ u, edgeSection (eichlerNormal n F) u i h functional s r
        ∂((volume : Measure ℝ).prod volume) :=
    funext fun r => radicalEdge_eq_integral large hF _ _ h functional
  rw [integral]
  exact (hasDerivAt_integral_edgeSection large hF i h functional s).deriv

/-- **The derivative of an edge component along the diagonal flow.** -/
theorem hasDerivAt_edgeComponent_diagonal (large : 5 ≤ n) (hF : EichlerData n F) (i : Fin 2)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    HasDerivAt (fun s => edgeComponent (lineTransferCochain (eichlerNormal n F)) (diagonalFlow s)
      i (h, functional)) (edgeMixedIntegral (eichlerNormal n F) i (h, functional)) 0 :=
  (hasDerivAt_integral_sectionDerivative large hF i h functional).congr_of_eventuallyEq
    (Eventually.of_forall fun s => edgeComponent_diagonal_eq large hF i h functional s)

/-! ### The coordinates of the derivative edge -/

theorem coord_lowerRadicalCoordinate_lineVector (V : Fin 2 → LineValues n) (h : BinaryAdelicGL)
    (j : Fin (n + 2)) :
    (binaryWeightBasis (n + 1)).coord j (lowerRadicalCoordinate n (fun i => lineVector (V i) h)) =
      ∑ i, ∑ k, V i (h, (homogeneousBasis n).coord k) *
        (binaryWeightBasis (n + 1)).coord j
          (lowerRadicalCoordinate n (Pi.single i (homogeneousBasis n k))) := by
  have expansion : (fun i => lineVector (V i) h) = ∑ i, ∑ k,
      V i (h, (homogeneousBasis n).coord k) • Pi.single i (homogeneousBasis n k) := by
    funext i'
    simp only [lineVector, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite,
      smul_zero]
    rw [Finset.sum_comm]
    simp
  rw [expansion]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- **The coordinates of the derivative edge along the diagonal flow.** -/
theorem hasDerivAt_coord_derivativeEdge_diagonal (large : 5 ≤ n) (hF : EichlerData n F)
    (h : BinaryAdelicGL) (j : Fin (n + 2)) :
    HasDerivAt (fun s => (binaryWeightBasis (n + 1)).coord j
        (derivativeEdge (lineTransferCochain (eichlerNormal n F)) (diagonalFlow s) h))
      ((binaryWeightBasis (n + 1)).coord j (lowerRadicalCoordinate n
        (fun i => lineVector (edgeMixedIntegral (eichlerNormal n F) i) h))) 0 := by
  unfold derivativeEdge
  simp only [coord_lowerRadicalCoordinate_lineVector]
  exact HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun k _ =>
    (hasDerivAt_edgeComponent_diagonal large hF i h _).mul_const _

end TernaryPeriodPolynomials.AnalyticClasses
