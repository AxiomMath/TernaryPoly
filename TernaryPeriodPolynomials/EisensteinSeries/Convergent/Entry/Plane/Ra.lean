module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Lift
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceInduced

@[expose] public section


/-!
# R-a: the plane integral cochain is a source cocycle

`cOmega_isSourceCocycle`: for the weighted scalar realization `F` of a smooth finite-level vector `v` of the cuspidal
representation (the Eichler datum) and a Levi cocycle `E` with `E.α = eichlerNormal n F`, the plane integral cochain
`cOmega n D F` satisfies all four clauses of `IsSourceCocycle D .plane`:
* the algebraic laws (finite level, covariance, the cocycle identity) from `cOmega = planeSource + δ planeEdge`
  (`cOmega_decomp`) and the library's laws of `planeSource`;
* the induced-section laws (unipotent, rank-one torus, `GL₂` Levi) from the translation law (`Entry/PlaneLaws`);
* the smooth cusp lifts and the real analyticity of the scalar coefficients from the explicit vector
  `OmegaVec` (`Entry/PlaneLift`), whose smooth dependence on the real parameters is the analytic parametric integral
  `analyticAt_param_integral`.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

section Assembly

variable {n : ℕ} (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ)
  (hol : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
  (E : LeviCocycleData D.cusp n) (hE : ∀ A, E.α A = eichlerNormal n F A)
  (hc : ∀ g : RealGL3, componentCharacter D.chi g = 1)
  (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)

include hol hE hc hχ

theorem cOmega_decomp (y : Fin 3 → RealGL3) (g : AdelicGL) :
    cOmega n D F y g = planeSource D E y g + (planeEdge D F hol ![y 1, y 2] g -
      planeEdge D F hol ![y 0, y 2] g + planeEdge D F hol ![y 0, y 1] g) := by
  rw [← cOmega_sub_planeSource D F hol E hE hc hχ y g]
  abel

theorem cOmega_level (k : finiteLevel) (y : Fin 3 → RealGL3) (g : AdelicGL) :
    cOmega n D F y (g * atFinite k.val) = cOmega n D F y g := by
  rw [cOmega_decomp D F hol E hE hc hχ, cOmega_decomp D F hol E hE hc hχ,
    planeEdge_level D F hol E hE hc hχ, planeEdge_level D F hol E hE hc hχ, planeEdge_level D F hol E hE hc hχ]
  have : planeSource D E y (g * atFinite k.val) = planeSource D E y g :=
    planeSourceAt_level D E hχ g k y 1
  rw [this]

theorem cOmega_cov (h : RealGL3) (y : Fin 3 → RealGL3) (g : AdelicGL) :
    cOmega n D F (fun i => h * y i) g = realCoefficientComponent n D.chi h (cOmega n D F y (g * atInfinity h)) := by
  have hs := (planeSource_isSourceCocycle D E hχ).2.2.1 h y g
  rw [cOmega_decomp D F hol E hE hc hχ, cOmega_decomp D F hol E hE hc hχ y (g * atInfinity h)]
  simp only [map_add, map_sub]
  have e : ∀ i j : Fin 3, (![h * y i, h * y j] : Fin 2 → RealGL3) = fun k => h * (![y i, y j] : Fin 2 → RealGL3) k := by
    intro i j; funext k; fin_cases k <;> rfl
  have b := fun (i j : Fin 3) => planeEdge_cov D F hol E hE hc hχ h ![y i, y j] g
  have c1 : planeEdge D F hol ![h * y 1, h * y 2] g =
      realCoefficientComponent n D.chi h (planeEdge D F hol ![y 1, y 2] (g * atInfinity h)) := by
    rw [e 1 2]; exact b 1 2
  have c2 : planeEdge D F hol ![h * y 0, h * y 2] g =
      realCoefficientComponent n D.chi h (planeEdge D F hol ![y 0, y 2] (g * atInfinity h)) := by
    rw [e 0 2]; exact b 0 2
  have c3 : planeEdge D F hol ![h * y 0, h * y 1] g =
      realCoefficientComponent n D.chi h (planeEdge D F hol ![y 0, y 1] (g * atInfinity h)) := by
    rw [e 0 1]; exact b 0 1
  rw [c1, c2, c3]
  have : planeSource D E (fun i => h * y i) g = realCoefficientComponent n D.chi h
      (planeSource D E y (g * atInfinity h)) := hs
  rw [this]

theorem cOmega_decomp3 (a b c : RealGL3) (g : AdelicGL) :
    cOmega n D F ![a, b, c] g = planeSource D E ![a, b, c] g + (planeEdge D F hol ![b, c] g -
      planeEdge D F hol ![a, c] g + planeEdge D F hol ![a, b] g) :=
  cOmega_decomp D F hol E hE hc hχ ![a, b, c] g

theorem cOmega_cocycle (x : Fin 4 → RealGL3) (g : AdelicGL) :
    cOmega n D F ![x 1, x 2, x 3] g - cOmega n D F ![x 0, x 2, x 3] g + cOmega n D F ![x 0, x 1, x 3] g -
      cOmega n D F ![x 0, x 1, x 2] g = 0 := by
  have hs := (planeSource_isSourceCocycle D E hχ).2.2.2 x g
  rw [cOmega_decomp3 D F hol E hE hc hχ, cOmega_decomp3 D F hol E hE hc hχ, cOmega_decomp3 D F hol E hE hc hχ,
    cOmega_decomp3 D F hol E hE hc hχ]
  rw [← hs]
  abel


theorem cOmega_levi (A : BinaryAdelicGL) (g : AdelicGL) (y : Fin 3 → RealGL3) :
    cOmega n D F y (GeneralEisenstein.Adelic.planeLevi A 1 * g) =
      normPower (Matrix.GeneralLinearGroup.det A) (((n : ℂ) + 3) / 2) • cOmegaAt D F y g A := by
  rw [← cOmegaAt_one D F, cOmegaAt_levi D F hol E hE hc hχ, one_mul]

theorem cOmega_unipotent (a b : Adeles) (g : AdelicGL) (y : Fin 3 → RealGL3) :
    cOmega n D F y (GeneralEisenstein.Adelic.planeUnipotent a b * g) = cOmega n D F y g := by
  rw [← cOmegaAt_one D F, ← cOmegaAt_one D F, cOmegaAt_unipotent D F hol E hE hc hχ]

theorem cOmega_torus (t : Adelesˣ) (g : AdelicGL) (y : Fin 3 → RealGL3) :
    cOmega n D F y (GeneralEisenstein.Adelic.planeLevi 1 t * g) = D.chi.toMonoidHom t • cOmega n D F y g := by
  rw [← cOmegaAt_one D F, ← cOmegaAt_one D F, cOmegaAt_torus D F hol E hE hc hχ]

variable (stages : AnalyticScalar.ContinuousStages D.cusp) (hw : ℤ) (v : D.cusp.smooth)
  (fixed : v.val ∈ BinaryLevel.fixedSubspace D.cusp BinaryLevel.finiteCongruence)
  (hF : F = cuspScalarWeightedRealization D.cusp hw v)

include stages fixed hF

/-- **The smooth cusp lift of the plane integral cochain along a real-analytic family.** -/
theorem cOmega_liftLevi (m : Fin 3 →₀ ℕ) (a : AdelicGL) {K : ℕ} (X : (Fin K → RealGL3) → Fin 3 → RealGL3)
    (z : (Fin K → RealGL3) → RealGL3) (fz f0 f1 f2 : (Fin K → Mat3) → Mat3)
    (cz : ContDiff ℝ ⊤ fz) (c0 : ContDiff ℝ ⊤ f0) (c1 : ContDiff ℝ ⊤ f1) (c2 : ContDiff ℝ ⊤ f2)
    (hz : ∀ x, (z x).val = fz (fun i => (x i).val))
    (h0 : ∀ x, gramOf (X x 0) = f0 (fun i => (x i).val))
    (h1 : ∀ x, gramOf (X x 1) = f1 (fun i => (x i).val))
    (h2 : ∀ x, gramOf (X x 2) = f2 (fun i => (x i).val)) :
    ∃ w : (Fin K → RealGL3) → D.cusp.smooth, Smooth (fun x => (w x).val) ∧
      ∀ x A, D.cusp.realize (w x) A =
        normPower (Matrix.GeneralLinearGroup.det A) (-(((n : ℂ) + 3) / 2)) *
          (cOmega n D F (X x) (GeneralEisenstein.Adelic.planeLevi A 1 * (a * atInfinity (z x)))).val.coeff m := by
  subst hF
  obtain ⟨w, hw1, hw2⟩ := omega_lift_family D stages hw v fixed hol m a X z fz f0 f1 f2 cz c0 c1 c2 hz h0 h1 h2
  refine ⟨w, hw1, fun x A => ?_⟩
  rw [hw2, cOmega_levi D _ hol E hE hc hχ, Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul,
    ← mul_assoc, ps_normPower_neg_mul, one_mul]


theorem cOmega_hasSmoothCuspLift (m : Fin 3 →₀ ℕ) :
    HasSmoothCuspLift D .plane cohomologicalPoint (fun x g => (cOmega n D F x g).val.coeff m) := by
  intro a
  obtain ⟨w, hw1, hw2⟩ := cOmega_liftLevi D F hol E hE hc hχ stages hw v fixed hF m a (K := 3 + 1)
    (fun x i => x (Fin.castSucc i)) (fun x => x (Fin.last 3)) (fun A => A (Fin.last 3))
    (fun A => A (Fin.castSucc 0) * (A (Fin.castSucc 0))ᵀ) (fun A => A (Fin.castSucc 1) * (A (Fin.castSucc 1))ᵀ)
    (fun A => A (Fin.castSucc 2) * (A (Fin.castSucc 2))ᵀ)
    (contDiff_apply ℝ Mat3 (Fin.last 3))
    (contDiff_matMul (contDiff_apply ℝ Mat3 _) (contDiff_matTranspose (contDiff_apply ℝ Mat3 _)))
    (contDiff_matMul (contDiff_apply ℝ Mat3 _) (contDiff_matTranspose (contDiff_apply ℝ Mat3 _)))
    (contDiff_matMul (contDiff_apply ℝ Mat3 _) (contDiff_matTranspose (contDiff_apply ℝ Mat3 _)))
    (fun x => rfl) (fun x => rfl) (fun x => rfl) (fun x => rfl)
  refine ⟨w, hw1, fun x A => ?_⟩
  rw [hw2, plane_binExp]
  rfl

theorem cOmega_isInduced (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) :
    IsInduced D .plane cohomologicalPoint (fun g => (cOmega n D F y g).val.coeff m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    have := omega_scalar_smooth_family D F hol m g 1 (K := 1) (fun _ => y) (fun x => x 0) (fun A => A 0)
      (fun _ => gramOf (y 0)) (fun _ => gramOf (y 1)) (fun _ => gramOf (y 2))
      (contDiff_apply ℝ Mat3 (0 : Fin 1)) contDiff_const contDiff_const contDiff_const
      (fun x => rfl) (fun x => rfl) (fun x => rfl) (fun x => rfl)
    simpa only [cOmegaAt_one] using this
  · intro k g
    show (cOmega n D F y (g * atFinite k.val)).val.coeff m = (cOmega n D F y g).val.coeff m
    rw [cOmega_level D F hol E hE hc hχ]
  · intro a
    obtain ⟨w, hw1, hw2⟩ := cOmega_liftLevi D F hol E hE hc hχ stages hw v fixed hF m a (K := 0 + 1)
      (fun _ => y) (fun x => x (Fin.last 0)) (fun A => A (Fin.last 0))
      (fun _ => gramOf (y 0)) (fun _ => gramOf (y 1)) (fun _ => gramOf (y 2))
      (contDiff_apply ℝ Mat3 (Fin.last 0)) contDiff_const contDiff_const contDiff_const
      (fun x => rfl) (fun x => rfl) (fun x => rfl) (fun x => rfl)
    refine ⟨w, hw1, fun x A => ?_⟩
    rw [hw2, plane_binExp]
    rfl
  · refine ⟨?_, ?_, ?_⟩
    · intro a b g
      show (cOmega n D F y (GeneralEisenstein.Adelic.planeUnipotent a b * g)).val.coeff m =
        (cOmega n D F y g).val.coeff m
      rw [cOmega_unipotent D F hol E hE hc hχ]
    · intro t g
      show (cOmega n D F y (GeneralEisenstein.Adelic.planeLevi 1 t * g)).val.coeff m =
        D.chi.toMonoidHom t * normPower t (-2 * inductionExponent .plane cohomologicalPoint) *
          (cOmega n D F y g).val.coeff m
      rw [cOmega_torus D F hol E hE hc hχ, ind_exp_plane, mul_zero, ps_normPower_zero, mul_one,
        Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    · intro g
      unfold cuspFunctions
      obtain ⟨w, hw1, hw2⟩ := cOmega_liftLevi D F hol E hE hc hχ stages hw v fixed hF m g (K := 0 + 1)
        (fun _ => y) (fun x => x (Fin.last 0)) (fun A => A (Fin.last 0))
        (fun _ => gramOf (y 0)) (fun _ => gramOf (y 1)) (fun _ => gramOf (y 2))
        (contDiff_apply ℝ Mat3 (Fin.last 0)) contDiff_const contDiff_const contDiff_const
        (fun x => rfl) (fun x => rfl) (fun x => rfl) (fun x => rfl)
      refine LinearMap.mem_range.mpr ⟨w (fun _ => 1), ?_⟩
      funext A
      show D.cusp.realize (w (fun _ => 1)) A = _
      rw [hw2, ps_atInfinity_one, mul_one, ind_exp_plane, add_zero]

/-- **R-a: the plane integral cochain is a source cocycle.**  `F` is the weighted scalar realization of a smooth
finite-level vector `v` (the Eichler datum), `E` a Levi cocycle with `E.α = eichlerNormal n F`. -/
theorem cOmega_isSourceCocycle : IsSourceCocycle D .plane (fun y g => cOmega n D F y g) :=
  ⟨fun y m => cOmega_isInduced D F hol E hE hc hχ stages hw v fixed hF y m,
    fun m => cOmega_hasSmoothCuspLift D F hol E hE hc hχ stages hw v fixed hF m,
    fun h y g => cOmega_cov D F hol E hE hc hχ h y g,
    fun x g => cOmega_cocycle D F hol E hE hc hχ x g⟩

end Assembly

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
