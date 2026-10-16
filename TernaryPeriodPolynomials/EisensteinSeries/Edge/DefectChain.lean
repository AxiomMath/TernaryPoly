module

public import TernaryPeriodPolynomials.EisensteinSeries.Edge.Inputs
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.DefectRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.DefectCovariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.DefectAverage

@[expose] public section


/-!
# The defect translation family without a degree bound

Workstream F's analysis of the defect family `r ↦ (E c - c_side)(y)(u(K r) q⁻¹)` (cocycle law,
continuity, covariance, periodicity, vanishing torus averages), for an arbitrary line source cocycle
`line` in place of the standard continuation `J c`, and with the four analytic inputs of `Inputs`
in place of the absolute convergence `4 ≤ n`:

* regularity uses `EisensteinContinuous`;
* real covariance of the defect uses `SourceRealCovariant`;
* the plane and line averages use `PlaneConstantTermAtEdge` and `LineConstantTermAtEdge`.

The degree-free lemmas of `EisensteinGraph.ConstantTerm` are reused.

Original work by Claude Opus 5.5 (AxiomCode), generalizing AxiomCode's `ConstantTerm` chain (`DefectRegularity`, `DefectCovariance`, `DefectAverage`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous MeasureTheory
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein

open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

/-- The real image of a rational matrix, written out in full. -/
local notation:max "ratReal[" g "]" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g

variable {n : ℕ}

section Unfolding

variable (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
  (c : SourceSpace.sourceCocycles D .plane) (line : SourceSpace.sourceCocycles D .line)

theorem defectFamily_eq (side : Side) (q : RationalGL3) (K : ℕ) (r : ℝ × ℝ)
    (y : Fin 3 → RationalGL3) :
    defectFamily D hol c line side q K r y =
      ConstantTerm.eisensteinValue D hol c (GlobalEisensteinCocycle.realVertices y)
          (atInfinity (ConstantTerm.sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) *
            rationalGroup q⁻¹) -
        (sideSource D c line side).val (GlobalEisensteinCocycle.realVertices y)
          (atInfinity (ConstantTerm.sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) *
            rationalGroup q⁻¹) := rfl

theorem defectFamily_eq_value (side : Side) (q : RationalGL3) (K : ℕ) (r : ℝ × ℝ)
    (y : Fin 3 → RationalGL3) :
    defectFamily D hol c line side q K r y =
      defectValue D hol c line side (GlobalEisensteinCocycle.realVertices y)
        (ConstantTerm.translationArgument side q K r) := rfl

theorem sideSource_plane : sideSource D c line .plane = c := rfl

theorem sideSource_line : sideSource D c line .line = line := rfl

end Unfolding

/-! ## Regularity -/

section Regularity

variable (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
  (c : SourceSpace.sourceCocycles D .plane) (line : SourceSpace.sourceCocycles D .line)

/-- **Cocycle law** of the defect family in the vertex tuple. -/
theorem defectFamily_isCocycle₂ (side : Side) (q : RationalGL3) (K : ℕ) (r : ℝ × ℝ) :
    ConstantTerm.IsCocycle₂ (defectFamily D hol c line side q K r) := by
  intro x
  simp only [defectFamily_eq]
  exact ConstantTerm.four_term_sub _ _ _ _ _ _ _ _ (ConstantTerm.eisensteinValue_fourTerm D hol c x _)
    (ConstantTerm.sourceCocycle_fourTerm (sideSource D c line side) x _)

/-- Continuity of each monomial coefficient of the defect family in the parameter. -/
theorem defectFamily_coeff_continuous (cont : EisensteinContinuous D hol) (side : Side)
    (q : RationalGL3) (K : ℕ) (y : Fin 3 → RationalGL3) (m : Fin 3 →₀ ℕ) :
    Continuous (fun r : ℝ × ℝ =>
      (defectFamily D hol c line side q K r y).val.coeff m) := by
  have hg := ConstantTerm.defectArgument_continuous side q K
  have e : (fun r : ℝ × ℝ => (defectFamily D hol c line side q K r y).val.coeff m) =
      fun r : ℝ × ℝ =>
        (SectionSpace.sectionEisensteinValue D hol
          (PolynomialEisenstein.coefficientSection D m
            (PolynomialEisenstein.sourceSection D c
              (GlobalEisensteinCocycle.realVertices y)))).val
          (atInfinity (ConstantTerm.sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) *
            rationalGroup q⁻¹) -
        ((sideSource D c line side).val
          (GlobalEisensteinCocycle.realVertices y)
          (atInfinity (ConstantTerm.sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) *
            rationalGroup q⁻¹)).val.coeff m := by
    funext r
    rw [defectFamily_eq, Submodule.coe_sub, MvPolynomial.coeff_sub]
    congr 1
    exact PolynomialNaturality.polynomialValue_coeff D hol
      (PolynomialEisenstein.sourceSection D c (GlobalEisensteinCocycle.realVertices y)) m _
  rw [e]
  exact ((cont _).comp hg).sub
    ((InducedContinuity.induced_continuous D side cohomologicalPoint _
      ((sideSource D c line side).property.1 (GlobalEisensteinCocycle.realVertices y) m)).comp hg)

/-- **Continuity** of every linear functional of the defect family in the parameter. -/
theorem defectFamily_functional_continuous (cont : EisensteinContinuous D hol) (side : Side)
    (q : RationalGL3) (K : ℕ) (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Continuous (fun r : ℝ × ℝ => μ (defectFamily D hol c line side q K r y)) := by
  obtain ⟨weight, hweight⟩ := FlagExactness.homogeneous_functional_eq_sum n μ
  simp_rw [hweight]
  exact continuous_finsetSum _ (fun s _ =>
    (defectFamily_coeff_continuous D hol c line cont side q K y s.val).mul continuous_const)

theorem defectFamily_regularity (cont : EisensteinContinuous D hol) (side : Side)
    (q : RationalGL3) (K : ℕ) :
    (∀ r : ℝ × ℝ, ConstantTerm.IsCocycle₂ (defectFamily D hol c line side q K r)) ∧
      ∀ (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ),
        Continuous (fun r : ℝ × ℝ => μ (defectFamily D hol c line side q K r y)) :=
  ⟨defectFamily_isCocycle₂ D hol c line side q K,
    defectFamily_functional_continuous D hol c line cont side q K⟩

end Regularity

/-! ## Covariance -/

section Covariance

variable (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
  (c : SourceSpace.sourceCocycles D .plane) (cov : SourceRealCovariant D hol c)
  (line : SourceSpace.sourceCocycles D .line)

include cov in
/-- Real covariance of the defect. -/
theorem defectValue_real_covariant (side : Side) (h : RealGL3) (x : Fin 3 → RealGL3)
    (a : AdelicGL) :
    defectValue D hol c line side (fun i => h * x i) a =
      realCoefficientComponent n D.chi h (defectValue D hol c line side x (a * atInfinity h)) := by
  have hs := (sideSource D c line side).property
  simp only [defectValue, ConstantTerm.eisensteinValue]
  rw [cov h x a, hs.2.2.1 h x a, map_sub]

/-- Left invariance of the defect under the rational points of the parabolic of the side. -/
theorem defectValue_rational_left (side : Side) (p : RationalGL3) (hp : p ∈ parabolic side)
    (x : Fin 3 → RealGL3) (a : AdelicGL) :
    defectValue D hol c line side x (rationalGroup p * a) =
      defectValue D hol c line side x a := by
  have hs := (sideSource D c line side).property
  simp only [defectValue, ConstantTerm.eisensteinValue, GlobalEisensteinCocycle.sourceValueAtReal]
  rw [PolynomialEisenstein.polynomialValue_rational,
    RationalComparison.source_parabolicInvariant D RationalNorm.rational_norm side _ hs p hp x a]

/-- Right invariance of the defect under the finite level. -/
theorem defectValue_finite_right (side : Side) (k : finiteLevel) (x : Fin 3 → RealGL3)
    (a : AdelicGL) :
    defectValue D hol c line side x (a * atFinite k.val) =
      defectValue D hol c line side x a := by
  have hs := (sideSource D c line side).property
  simp only [defectValue, ConstantTerm.eisensteinValue, GlobalEisensteinCocycle.sourceValueAtReal]
  rw [PolynomialEisenstein.polynomialValue_finite D hol _ k a,
    Comparison.source_finiteInvariant D side _ hs k x a]

theorem defectValue_absorb (side : Side) (p : RationalGL3) (hp : p ∈ parabolic side)
    (k : RationalGL3) (hk : k ∈ rationalLevel) (x : Fin 3 → RealGL3) (B : AdelicGL) :
    defectValue D hol c line side x (rationalGroup p * B * atFinite (rationalFinite k)) =
      defectValue D hol c line side x B := by
  have hfin : rationalFinite k ∈ finiteLevel := Comparison.rationalLevel_finiteLevel ⟨k, hk⟩
  have h1 := defectValue_finite_right D hol c line side ⟨rationalFinite k, hfin⟩ x
    (rationalGroup p * B)
  have h2 := defectValue_rational_left D hol c line side p hp x B
  exact h1.trans h2

include cov in
theorem defectFamily_mul_vertices (side : Side) (q : RationalGL3) (K : ℕ) (r : ℝ × ℝ)
    (g : RationalGL3) (y : Fin 3 → RationalGL3) :
    defectFamily D hol c line side q K r (fun i => g * y i) =
      rationalCoefficientComponent n D.chi g
        (defectValue D hol c line side (GlobalEisensteinCocycle.realVertices y)
          (ConstantTerm.translationArgument side q K r * atInfinity (ratReal[g]))) := by
  have h := defectValue_real_covariant D hol c cov line side (ratReal[g])
    (GlobalEisensteinCocycle.realVertices y) (ConstantTerm.translationArgument side q K r)
  rw [defectFamily_eq_value, ConstantTerm.realVertices_leftMul]
  exact h

include cov in
/-- **Shift.** -/
theorem defectFamily_shift (side : Side) (q : RationalGL3) (K : ℕ) (w : ℚ × ℚ) (r : ℝ × ℝ)
    (y : Fin 3 → RationalGL3) :
    defectFamily D hol c line side q K r
        (fun i => (q * ConstantTerm.sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2) * q⁻¹) *
          y i) =
      rationalCoefficientComponent n D.chi
        (q * ConstantTerm.sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2) * q⁻¹)
        (defectFamily D hol c line side q K (r.1 + (w.1 : ℝ), r.2 + (w.2 : ℝ)) y) := by
  rw [defectFamily_mul_vertices D hol c cov line, ConstantTerm.translationArgument_shift,
    defectFamily_eq_value]

include cov in
/-- **Levi covariance.** -/
theorem defectFamily_levi (side : Side) (q : RationalGL3) (K : ℕ) (γ : RationalGL3)
    (hγ : γ ∈ rationalLevel) (hp : q⁻¹ * γ * q ∈ parabolic side) (r r' : ℝ × ℝ)
    (hr : (ratReal[q⁻¹ * γ * q])⁻¹ *
        ConstantTerm.sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2) *
        ratReal[q⁻¹ * γ * q] =
      ConstantTerm.sideUnipotent side ((K : ℝ) * r'.1) ((K : ℝ) * r'.2))
    (y : Fin 3 → RationalGL3) :
    defectFamily D hol c line side q K r (fun i => γ * y i) =
      rationalCoefficientComponent n D.chi γ (defectFamily D hol c line side q K r' y) := by
  have hcore := ConstantTerm.translationArgument_levi side q (q⁻¹ * γ * q) K r r' hr
  rw [show q * (q⁻¹ * γ * q) * q⁻¹ = γ by group] at hcore
  rw [defectFamily_mul_vertices D hol c cov line, hcore,
    defectValue_absorb D hol c line side (q⁻¹ * γ * q) hp γ⁻¹ (rationalLevel.inv_mem hγ),
    defectFamily_eq_value]

/-- **Periodicity.** -/
theorem defectFamily_periodic (side : Side) (q : RationalGL3) (K : ℕ) (w : ℚ × ℚ)
    (hw : q * ConstantTerm.sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2) * q⁻¹ ∈
      rationalLevel)
    (r : ℝ × ℝ) (y : Fin 3 → RationalGL3) :
    defectFamily D hol c line side q K (r.1 + (w.1 : ℝ), r.2 + (w.2 : ℝ)) y =
      defectFamily D hol c line side q K r y := by
  have hcomm : (ratReal[ConstantTerm.sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2)])⁻¹ *
      ConstantTerm.sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2) *
        ratReal[ConstantTerm.sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2)] =
      ConstantTerm.sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2) := by
    rw [ConstantTerm.map_sideUnipotent_scaled, mul_assoc,
      ConstantTerm.sideUnipotent_comm side ((K : ℝ) * r.1) ((K : ℝ) * r.2)
        ((K : ℝ) * (w.1 : ℝ)) ((K : ℝ) * (w.2 : ℝ)),
      inv_mul_cancel_left]
  have hshift := ConstantTerm.translationArgument_shift side q K w r
  have hlevi := ConstantTerm.translationArgument_levi side q
    (ConstantTerm.sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2)) K r r hcomm
  rw [defectFamily_eq_value, defectFamily_eq_value, ← hshift, hlevi]
  exact defectValue_absorb D hol c line side _ (ConstantTerm.sideUnipotent_mem_parabolic side _ _)
    _ (rationalLevel.inv_mem hw) _ _

theorem defectFamily_periodic_int (side : Side) (q : RationalGL3) (K : ℕ) (ℓ : ℤ × ℤ)
    (hℓ : q * ConstantTerm.sideUnipotent side ((K : ℚ) * (ℓ.1 : ℚ)) ((K : ℚ) * (ℓ.2 : ℚ)) * q⁻¹ ∈
      rationalLevel)
    (r : ℝ × ℝ) (y : Fin 3 → RationalGL3) :
    defectFamily D hol c line side q K (r.1 + (ℓ.1 : ℝ), r.2 + (ℓ.2 : ℝ)) y =
      defectFamily D hol c line side q K r y := by
  have h := defectFamily_periodic D hol c line side q K ((ℓ.1 : ℚ), (ℓ.2 : ℚ)) hℓ r y
  simpa only [Rat.cast_intCast] using h

end Covariance

/-! ## Vanishing of the torus averages -/

section Average

variable (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
  (c : SourceSpace.sourceCocycles D .plane) (line : SourceSpace.sourceCocycles D .line)

theorem defectFamily_three (side : Side) (q : RationalGL3) (r : ℝ × ℝ)
    (y : Fin 3 → RationalGL3) :
    defectFamily D hol c line side q 3 r y =
      defectValue D hol c line side (GlobalEisensteinCocycle.realVertices y)
        (atInfinity (ConstantTerm.sideUnipotent side (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹) :=
  rfl

theorem defectValue_coeff (side : Side) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (g : AdelicGL) :
    (defectValue D hol c line side y g).val.coeff m =
      (ConstantTerm.eisensteinValue D hol c y g).val.coeff m -
        ((sideSource D c line side).val y g).val.coeff m := by
  unfold defectValue
  rw [Submodule.coe_sub, MvPolynomial.coeff_sub]

theorem line_path_invariant (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (a b : ℝ) (g : AdelicGL) :
    (line.val y (atInfinity (lineUnipotent a b) * g)).val.coeff m =
      (line.val y g).val.coeff m := by
  rw [ConstantTerm.DefectAverage.atInfinity_lineUnipotent_eq]
  exact ConstantTerm.DefectAverage.isInduced_line_unipotent (line.property.1 y m) (a, 0) (b, 0) g

/-- Real plane average of the Eisenstein coefficient: the coefficient of `c`. -/
theorem coefficient_plane_real_average (cont : EisensteinContinuous D hol)
    (planeCT : PlaneConstantTermAtEdge D hol) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ)
    (integral : GL3 IntegralAdeles) (g : AdelicGL)
    (finite_eq : finiteGroup g = Matrix.GeneralLinearGroup.map integralEmbedding integral) :
    (∫ r : ℝ × ℝ, ConstantTerm.DefectAverage.eisensteinCoefficient D hol c y m
        (atInfinity (planeUnipotent (3 * r.1) (3 * r.2)) * g) ∂realPlaneUnitMeasure) =
      (c.val y g).val.coeff m :=
  (ConstantTerm.DefectAverage.plane_real_average_eq_adelic (F := ConstantTerm.DefectAverage.eisensteinCoefficient D hol c y m)
    (cont (PolynomialEisenstein.coefficientSection D m (PolynomialEisenstein.sourceSection D c y)))
    (ConstantTerm.DefectAverage.eisensteinCoefficient_rational D hol c y m) (ConstantTerm.DefectAverage.eisensteinCoefficient_finite D hol c y m)
    integral g finite_eq).trans
    (planeCT (PolynomialEisenstein.coefficientSection D m (PolynomialEisenstein.sourceSection D c y))
      g)

/-- The line coefficients are the line constant terms of the Eisenstein coefficients. -/
theorem line_coeff_eq_integral (lineCT : LineConstantTermAtEdge D hol c line)
    (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (g : AdelicGL) :
    (line.val y g).val.coeff m =
      ∫ point : Adeles × Adeles, ConstantTerm.DefectAverage.eisensteinCoefficient D hol c y m
        (lineUnipotent point.1 point.2 * g) ∂planeDomainMeasure := by
  rw [lineCT y g m, planeDomainMeasure_eq]
  refine integral_congr_ae (ae_of_all _ fun point => ?_)
  exact PolynomialNaturality.polynomialValue_coeff D hol
    (PolynomialEisenstein.sourceSection D c y) m _

/-- Real line average of the Eisenstein coefficient: the coefficient of `line`. -/
theorem coefficient_line_real_average (cont : EisensteinContinuous D hol)
    (lineCT : LineConstantTermAtEdge D hol c line) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ)
    (integral : GL3 IntegralAdeles) (g : AdelicGL)
    (finite_eq : finiteGroup g = Matrix.GeneralLinearGroup.map integralEmbedding integral) :
    (∫ r : ℝ × ℝ, ConstantTerm.DefectAverage.eisensteinCoefficient D hol c y m
        (atInfinity (lineUnipotent (3 * r.1) (3 * r.2)) * g) ∂realPlaneUnitMeasure) =
      (line.val y g).val.coeff m :=
  (ConstantTerm.DefectAverage.line_real_average_eq_adelic (F := ConstantTerm.DefectAverage.eisensteinCoefficient D hol c y m)
    (cont (PolynomialEisenstein.coefficientSection D m (PolynomialEisenstein.sourceSection D c y)))
    (ConstantTerm.DefectAverage.eisensteinCoefficient_rational D hol c y m) (ConstantTerm.DefectAverage.eisensteinCoefficient_finite D hol c y m)
    integral g finite_eq).trans (line_coeff_eq_integral D hol c line lineCT y m g).symm

/-- Plane stratum: the real torus average of the defect family vanishes. -/
theorem defectFamily_plane_average_zero (cont : EisensteinContinuous D hol)
    (planeCT : PlaneConstantTermAtEdge D hol) (q : RationalGL3) (integral : GL3 IntegralAdeles)
    (hq : finiteGroup (rationalGroup q⁻¹) =
      Matrix.GeneralLinearGroup.map integralEmbedding integral)
    (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (∫ r : ℝ × ℝ, μ (defectFamily D hol c line .plane q 3 r y) ∂realPlaneUnitMeasure) = 0 := by
  refine ConstantTerm.DefectAverage.average_zero_of_coefficients μ
    (fun r => defectFamily D hol c line .plane q 3 r y)
    (fun m r => ConstantTerm.DefectAverage.eisensteinCoefficient D hol c (GlobalEisensteinCocycle.realVertices y) m
      (atInfinity (planeUnipotent (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹))
    (fun m => (c.val (GlobalEisensteinCocycle.realVertices y) (rationalGroup q⁻¹)).val.coeff m)
    ?_ ?_ ?_
  · intro r m
    show (defectFamily D hol c line .plane q 3 r y).val.coeff m =
      ConstantTerm.DefectAverage.eisensteinCoefficient D hol c (GlobalEisensteinCocycle.realVertices y) m
        (atInfinity (planeUnipotent (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹) -
      (c.val (GlobalEisensteinCocycle.realVertices y) (rationalGroup q⁻¹)).val.coeff m
    rw [defectFamily_three, defectValue_coeff, ConstantTerm.DefectAverage.sideUnipotent_plane, ConstantTerm.DefectAverage.eisensteinValue_coeff,
      sideSource_plane, ConstantTerm.DefectAverage.source_plane_path_invariant]
  · intro m
    exact ConstantTerm.DefectAverage.integrable_realPlaneUnit_of_continuous
      ((cont (PolynomialEisenstein.coefficientSection D m (PolynomialEisenstein.sourceSection D c
        (GlobalEisensteinCocycle.realVertices y)))).comp (ConstantTerm.DefectAverage.continuous_planePath (rationalGroup q⁻¹)))
  · intro m
    exact coefficient_plane_real_average D hol c cont planeCT _ m integral _ hq

/-- Line stratum: the same vanishing, with `line` in place of `c`. -/
theorem defectFamily_line_average_zero (cont : EisensteinContinuous D hol)
    (lineCT : LineConstantTermAtEdge D hol c line) (q : RationalGL3)
    (integral : GL3 IntegralAdeles)
    (hq : finiteGroup (rationalGroup q⁻¹) =
      Matrix.GeneralLinearGroup.map integralEmbedding integral)
    (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (∫ r : ℝ × ℝ, μ (defectFamily D hol c line .line q 3 r y) ∂realPlaneUnitMeasure) = 0 := by
  refine ConstantTerm.DefectAverage.average_zero_of_coefficients μ
    (fun r => defectFamily D hol c line .line q 3 r y)
    (fun m r => ConstantTerm.DefectAverage.eisensteinCoefficient D hol c (GlobalEisensteinCocycle.realVertices y) m
      (atInfinity (lineUnipotent (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹))
    (fun m => (line.val (GlobalEisensteinCocycle.realVertices y) (rationalGroup q⁻¹)).val.coeff m)
    ?_ ?_ ?_
  · intro r m
    show (defectFamily D hol c line .line q 3 r y).val.coeff m =
      ConstantTerm.DefectAverage.eisensteinCoefficient D hol c (GlobalEisensteinCocycle.realVertices y) m
        (atInfinity (lineUnipotent (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹) -
      (line.val (GlobalEisensteinCocycle.realVertices y) (rationalGroup q⁻¹)).val.coeff m
    rw [defectFamily_three, defectValue_coeff, ConstantTerm.DefectAverage.sideUnipotent_line, ConstantTerm.DefectAverage.eisensteinValue_coeff,
      sideSource_line, line_path_invariant]
  · intro m
    exact ConstantTerm.DefectAverage.integrable_realPlaneUnit_of_continuous
      ((cont (PolynomialEisenstein.coefficientSection D m (PolynomialEisenstein.sourceSection D c
        (GlobalEisensteinCocycle.realVertices y)))).comp (ConstantTerm.DefectAverage.continuous_linePath (rationalGroup q⁻¹)))
  · intro m
    exact coefficient_line_real_average D hol c line cont lineCT _ m integral _ hq

/-- Both strata at an integral flag representative `g`, over the closed unit square. -/
theorem defectFamily_average_zero_Icc (cont : EisensteinContinuous D hol)
    (planeCT : PlaneConstantTermAtEdge D hol) (lineCT : LineConstantTermAtEdge D hol c line)
    (side : Side) (g : IntegralGL3) (y : Fin 3 → RationalGL3)
    (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (∫ r in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      μ (defectFamily D hol c line side
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g) 3 r y)) = 0 := by
  rw [← ConstantTerm.DefectAverage.realPlaneUnitMeasure_eq_Icc]
  cases side
  · exact defectFamily_plane_average_zero D hol c line cont planeCT _ _
      (ConstantTerm.DefectAverage.finiteGroup_rationalGroup_integral_inv g) y μ
  · exact defectFamily_line_average_zero D hol c line cont lineCT _ _
      (ConstantTerm.DefectAverage.finiteGroup_rationalGroup_integral_inv g) y μ

end Average

end TernaryPeriodPolynomials.EdgeEisenstein
