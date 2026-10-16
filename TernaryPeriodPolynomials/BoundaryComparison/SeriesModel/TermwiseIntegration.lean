module

public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.GramCochain

@[expose] public section


/-!
# Termwise integration of the Eisenstein series over Gram triangles

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise MatrixGroups ContDiff
open Matrix MeasureTheory Set

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeriesModel

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.FormCochainBridge
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) {Fm : Type*} [FunLike Fm UpperHalfPlane ℂ]
  (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic] (n : ℕ)
  [CuspFormClass Fm Λ ((n + 3 : ℕ) : ℤ)] (f : Fm) (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ)

/-- The value of the pulled-back series form on a pair of tangent vectors of the cone. -/
theorem gramForm_pair (x : Mat3) (hx : x ∈ gramCone) (u v : Mat3) :
    (gramForm Γ (gammaRho Γ n) (planeEisensteinInv Γ Λ n f hn hLevi) : TernaryPoly.SmoothLocalDeRham.RawForm Mat3 (Coef n) 2)
        x ![u, v] =
      ∑ a, ∑ b, (fderiv ℝ conePoint x u a * fderiv ℝ conePoint x v b) •
        Coef.mk (planeEisenstein Γ n f (conePoint x) a b) := by
  have hΩ : conePoint x ∈ Omega := conePoint_mem hx
  change (pullBack isOpen_gramCone contDiffOn_conePoint (fun _ hG => conePoint_mem hG) 2
    ((planeEisensteinInv Γ Λ n f hn hLevi : ZigZag.invClosed isOpen_Omega (gammaAct Γ) (gammaRho Γ n)) :
      TernaryPoly.SmoothLocalDeRham.Form (F := Coef n) Omega 2) : TernaryPoly.SmoothLocalDeRham.RawForm Mat3 (Coef n) 2) x ![u, v] = _
  rw [pullBack_apply isOpen_gramCone contDiffOn_conePoint (fun _ hG => conePoint_mem hG) _ hx]
  unfold TernaryPoly.SmoothCoveringDeRham.pullRaw
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have e : (⇑(fderiv ℝ conePoint x) ∘ ![u, v]) = ![fderiv ℝ conePoint x u, fderiv ℝ conePoint x v] := by
    funext i; fin_cases i <;> rfl
  refine Eq.trans (congrArg _ e) ?_
  change ((planeEisensteinComponents Γ Λ n f hn hLevi).form : TernaryPoly.SmoothLocalDeRham.RawForm (Fin 5 → ℝ) (Coef n) 2)
    (conePoint x) _ = _
  rw [(planeEisensteinComponents Γ Λ n f hn hLevi).form_apply hΩ]
  change altCLM (fun a b => (planeEisensteinComponents Γ Λ n f hn hLevi).comp (conePoint x) a b) _ = _
  rw [altCLM_apply, altRaw_apply_of_antisymm _ ((planeEisensteinComponents Γ Λ n f hn hLevi).anti _)]
  rfl

instance countableSL3 : Countable (Matrix.SpecialLinearGroup (Fin 3) ℤ) :=
  haveI : Countable (Matrix (Fin 3) (Fin 3) ℤ) := inferInstanceAs (Countable (Fin 3 → Fin 3 → ℤ))
  Function.Injective.countable (f := fun A : Matrix.SpecialLinearGroup (Fin 3) ℤ => (A : Matrix (Fin 3) (Fin 3) ℤ))
    Subtype.val_injective

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass Fm Λ ((n + 3 : ℕ) : ℤ)] in
/-- Termwise integration over a triangle: a normally convergent series of functions continuous on the triangle may be
integrated termwise. -/
theorem integral_tsum_tri {ι : Type*} [Countable ι] (g : ι → ℝ × ℝ → ℂ) (B : ι → ℝ) (hB : Summable B)
    (hc : ∀ i, ContinuousOn (g i) stdTriangle) (hb : ∀ i, ∀ q ∈ stdTriangle, ‖g i q‖ ≤ B i) :
    ∫ q in stdTriangle, ∑' i, g i q = ∑' i, ∫ q in stdTriangle, g i q := by
  have hint : ∀ i, Integrable (g i) (volume.restrict stdTriangle) := fun i =>
    (hc i).integrableOn_compact isCompact_stdTriangle
  have hvol : volume stdTriangle < ⊤ := isCompact_stdTriangle.measure_lt_top
  have hnorm : ∀ i, ∫ q in stdTriangle, ‖g i q‖ ≤ B i * (volume stdTriangle).toReal := by
    intro i
    calc ∫ q in stdTriangle, ‖g i q‖ ≤ ∫ _q in stdTriangle, B i :=
          setIntegral_mono_on (hint i).norm (integrableOn_const hvol.ne) measurableSet_stdTriangle
            (fun q hq => hb i q hq)
      _ = B i * (volume stdTriangle).toReal := by
          rw [setIntegral_const]; simp [mul_comm, Measure.real]
  have hsum : Summable fun i => ∫ q in stdTriangle, ‖g i q‖ :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg fun q => norm_nonneg _) hnorm (hB.mul_right _)
  exact (integral_tsum_of_summable_integral_norm hint hsum).symm

/-- The `c`-th term of the Gram-triangle integrand (coefficient `m`): the pullback to the triangle point `q` of the term of the coset
`c`, evaluated on the edge vectors of the triangle. -/
def gTerm (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ) {Fm : Type*} [FunLike Fm UpperHalfPlane ℂ]
    (f : Fm) (c : PlaneCoset Γ) (m : Fin 3 →₀ ℕ) (y : Fin 3 → GeneralEisenstein.RealGL3) (q : ℝ × ℝ) : ℂ :=
  ∑ a, ∑ b, ((fderiv ℝ conePoint (affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q)
      (gramOf (y 1) - gramOf (y 0)) a *
    fderiv ℝ conePoint (affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q)
      (gramOf (y 2) - gramOf (y 0)) b : ℝ) : ℂ) *
    termFun Γ n f c a b m (conePoint (affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q))

/-- **Termwise integration (OB7 step (b)).**  The coefficient `m` of the Gram-triangle cochain of the Eisenstein series is the sum over
the cosets `Γ_P\Γ` of the Gram-triangle integrals of the terms `ρ(γ)⁻¹ γ^* ω_h`. -/
theorem coeff_gramCochain_tsum (y : Fin 3 → GeneralEisenstein.RealGL3) (m : Fin 3 →₀ ℕ) :
    (Coef.toPoly (gramCochain Γ n (planeEisensteinInv Γ Λ n f hn hLevi) y)).coeff m =
      ∑' c : PlaneCoset Γ, ∫ q in stdTriangle, gTerm Γ n f c m y q := by
  classical
  let Cℂ : Coef n →ₗ[ℂ] ℂ := (MvPolynomial.lcoeff ℂ m).comp (Submodule.subtype _)
  let CR : Coef n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Cℂ.restrictScalars ℝ)
  have hCR : ∀ z : Coef n, CR z = (Coef.toPoly z).coeff m := fun z => rfl
  set p0 := gramOf (y 0) with hp0
  set p1 := gramOf (y 1) with hp1
  set p2 := gramOf (y 2) with hp2
  have hc0 : p0 ∈ gramCone := gramOf_mem_gramCone (y 0)
  have hc1 : p1 ∈ gramCone := gramOf_mem_gramCone (y 1)
  have hc2 : p2 ∈ gramCone := gramOf_mem_gramCone (y 2)
  have hpt : ∀ q ∈ stdTriangle, affTri p0 p1 p2 q ∈ gramCone := fun q hq =>
    affTri_mem convex_gramCone hc0 hc1 hc2 hq
  have hptc : Continuous (affTri p0 p1 p2) := continuous_affTri p0 p1 p2
  -- the compact set of chart points
  have hφc : ContinuousOn (fun q => conePoint (affTri p0 p1 p2 q)) stdTriangle :=
    contDiffOn_conePoint.continuousOn.comp hptc.continuousOn hpt
  have hK : IsCompact ((fun q => conePoint (affTri p0 p1 p2 q)) '' stdTriangle) :=
    isCompact_stdTriangle.image_of_continuousOn hφc
  have hKΩ : ((fun q => conePoint (affTri p0 p1 p2 q)) '' stdTriangle) ⊆ Omega := by
    rintro _ ⟨q, hq, rfl⟩
    exact conePoint_mem (hpt q hq)
  obtain ⟨b, hbs, hbd⟩ := normal_convergence Γ Λ n f hn hK hKΩ 0
  have hT : ∀ (c : PlaneCoset Γ) (a b' : Fin 5) q, q ∈ stdTriangle →
      ‖termFun Γ n f c a b' m (conePoint (affTri p0 p1 p2 q))‖ ≤ b c := by
    intro c a b' q hq
    have := hbd c _ ⟨q, hq, rfl⟩ a b' m
    rwa [norm_iteratedFDeriv_zero] at this
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ stdTriangle := ⟨le_rfl, le_rfl, by norm_num⟩
  have hb0 : ∀ c, 0 ≤ b c := fun c => (norm_nonneg _).trans (hT c 0 0 (0, 0) h00)
  -- the derivative factors
  have hfd : ContinuousOn (fderiv ℝ conePoint) gramCone :=
    contDiffOn_conePoint.continuousOn_fderiv_of_isOpen isOpen_gramCone (by exact_mod_cast le_top)
  have hD : ∀ w : Mat3, ∀ a : Fin 5, ContinuousOn
      (fun q => fderiv ℝ conePoint (affTri p0 p1 p2 q) w a) stdTriangle := by
    intro w a
    have h1 : ContinuousOn (fun q => fderiv ℝ conePoint (affTri p0 p1 p2 q)) stdTriangle :=
      hfd.comp hptc.continuousOn hpt
    exact (continuous_apply a).comp_continuousOn (h1.clm_apply continuousOn_const)
  have hG : ContinuousOn (fun q => ∑ a : Fin 5, ∑ b' : Fin 5,
      |fderiv ℝ conePoint (affTri p0 p1 p2 q) (p1 - p0) a| *
        |fderiv ℝ conePoint (affTri p0 p1 p2 q) (p2 - p0) b'|) stdTriangle :=
    continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b' _ =>
      (hD _ a).abs.mul (hD _ b').abs
  obtain ⟨M, hM⟩ := isCompact_stdTriangle.exists_bound_of_continuousOn hG
  have hgb : ∀ c, ∀ q ∈ stdTriangle, ‖gTerm Γ n f c m y q‖ ≤ M * b c := by
    intro c q hq
    unfold gTerm
    calc _ ≤ ∑ a : Fin 5, ∑ b' : Fin 5, ‖((fderiv ℝ conePoint (affTri p0 p1 p2 q) (p1 - p0) a *
          fderiv ℝ conePoint (affTri p0 p1 p2 q) (p2 - p0) b' : ℝ) : ℂ) *
          termFun Γ n f c a b' m (conePoint (affTri p0 p1 p2 q))‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ a : Fin 5, ∑ b' : Fin 5, |fderiv ℝ conePoint (affTri p0 p1 p2 q) (p1 - p0) a| *
          |fderiv ℝ conePoint (affTri p0 p1 p2 q) (p2 - p0) b'| * b c := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b' _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (hT c a b' q hq) (by positivity)
      _ = (∑ a : Fin 5, ∑ b' : Fin 5, |fderiv ℝ conePoint (affTri p0 p1 p2 q) (p1 - p0) a| *
          |fderiv ℝ conePoint (affTri p0 p1 p2 q) (p2 - p0) b'|) * b c := by
          simp only [Finset.sum_mul]
      _ ≤ M * b c := by
          refine mul_le_mul_of_nonneg_right ?_ (hb0 c)
          have := hM q hq
          rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b' _ =>
            by positivity)] at this
  have hgc : ∀ c, ContinuousOn (gTerm Γ n f c m y) stdTriangle := by
    intro c
    unfold gTerm
    refine continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b' _ => ?_
    refine (Complex.continuous_ofReal.comp_continuousOn ((hD _ a).mul (hD _ b'))).mul ?_
    exact ((contDiffOn_termFun Γ Λ n f c a b' m).continuousOn.comp hφc (fun q hq => conePoint_mem (hpt q hq)))
  have hsum : ∀ (a b' : Fin 5) q, q ∈ stdTriangle →
      Summable fun c => termFun Γ n f c a b' m (conePoint (affTri p0 p1 p2 q)) := fun a b' q hq =>
    Summable.of_norm_bounded hbs (fun c => hT c a b' q hq)
  have hpoint : ∀ q ∈ stdTriangle,
      CR ((gramForm Γ (gammaRho Γ n) (planeEisensteinInv Γ Λ n f hn hLevi) :
          TernaryPoly.SmoothLocalDeRham.RawForm Mat3 (Coef n) 2) (affTri p0 p1 p2 q) ![p1 - p0, p2 - p0]) =
        ∑' c, gTerm Γ n f c m y q := by
    intro q hq
    rw [gramForm_pair Γ Λ n f hn hLevi _ (hpt q hq)]
    simp only [map_sum, map_smul, Complex.real_smul]
    simp only [hCR]
    have hco : ∀ a b' : Fin 5, (Coef.toPoly (Coef.mk (planeEisenstein Γ n f
        (conePoint (affTri p0 p1 p2 q)) a b'))).coeff m =
        ∑' c, termFun Γ n f c a b' m (conePoint (affTri p0 p1 p2 q)) := fun a b' =>
      coeff_planeEisenstein Γ n f _ a b' m
    simp only [hco]
    unfold gTerm
    rw [Summable.tsum_finsetSum fun a _ => ?_]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Summable.tsum_finsetSum fun b' _ => ?_]
      · refine Finset.sum_congr rfl fun b' _ => ?_
        rw [tsum_mul_left]
      · exact (hsum a b' q hq).mul_left _
    · exact summable_sum fun b' _ => (hsum a b' q hq).mul_left _
  rw [← hCR, show gramCochain Γ n (planeEisensteinInv Γ Λ n f hn hLevi) y =
      ∫ q in stdTriangle, (gramForm Γ (gammaRho Γ n) (planeEisensteinInv Γ Λ n f hn hLevi) :
          TernaryPoly.SmoothLocalDeRham.RawForm Mat3 (Coef n) 2) (affTri p0 p1 p2 q) ![p1 - p0, p2 - p0] from rfl]
  have hint : IntegrableOn (fun q => (gramForm Γ (gammaRho Γ n) (planeEisensteinInv Γ Λ n f hn hLevi) :
          TernaryPoly.SmoothLocalDeRham.RawForm Mat3 (Coef n) 2) (affTri p0 p1 p2 q) ![p1 - p0, p2 - p0])
        stdTriangle :=
    integrable_triInt convex_gramCone
      ((pullInv (coneEquiv Γ) (fun _ => rfl) (planeEisensteinInv Γ Λ n f hn hLevi) :
        ZigZag.invClosed isOpen_gramCone (coneAction Γ) (gammaRho Γ n)) :
        TernaryPoly.SmoothLocalDeRham.Form (F := Coef n) gramCone 2) hc0 hc1 hc2
  rw [← ContinuousLinearMap.integral_comp_comm CR hint]
  rw [setIntegral_congr_fun measurableSet_stdTriangle hpoint]
  exact integral_tsum_tri (gTerm Γ n f · m y) (fun c => M * b c) (hbs.mul_left M) hgc hgb