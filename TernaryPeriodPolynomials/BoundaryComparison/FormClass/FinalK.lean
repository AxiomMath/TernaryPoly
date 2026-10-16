module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.IntegralK

@[expose] public section


/-!
# Every cusp, both seed types: the printed intertwiner is the orbit sum

Formalized by Claude Sonnet 5.5.

`printedIntegrandB b` is the integrand for the section of the seed of type `b` (`b = false`: holomorphic seed; `b = true`: the conjugate seed,
coefficientwise complex conjugation `cxP b` of the section, the paper's `\\bar ω`).
* `printed_intertwiner_evalK`: for every `k ∈ SL₃(ℤ)` and both types, the integral `∫_{𝔸²} φ^b(w₀⁻¹u(s,t) g)`, `g = (1, ι(k⁻¹))`, is absolutely
  convergent and equals `lineA1K N k n f b`, the explicit coordinate of the line row `r_{k^{-1}Qk} ℰ^b`.
* `rLine_series_integralK`: with the `seriesLineCusp_printed` this is the printed line row at every pair `(h, h')` of plane cusps (`k = h' h⁻¹`).
* `printedIntegrand_adelicOf_ker`: right `K(N)`-invariance in `g`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.EisensteinDual TernaryPeriodPolynomials.Argument.GammaNFaces

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

theorem realGroup_adelicOf (gf : FiniteGL) : realGroup (adelicOf gf) = 1 := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  simp [realGroup, adelicOf, GeneralLinearGroup.map_apply, Matrix.one_apply]

theorem finiteGroup_adelicOf (gf : FiniteGL) : finiteGroup (adelicOf gf) = gf := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  simp [finiteGroup, adelicOf, GeneralLinearGroup.map_apply]

theorem realMatOf_unip_adelicOf (gf : FiniteGL) (u : Adeles × Adeles) :
    realMatOf (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOf gf) = gReal ![u.1.1, u.2.1] := by
  have := realMatOf_unip u
  unfold realMatOf at this ⊢
  rw [map_mul, realGroup_adelicOf, mul_one]
  rwa [mul_one, map_mul] at this

theorem finiteGroup_unip_adelicOf (gf : FiniteGL) (u : Adeles × Adeles) :
    finiteGroup (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOf gf) = gFin (u.1.2, u.2.2) * gf := by
  have := finiteGroup_unip u
  rw [map_mul, finiteGroup_adelicOf, ← this, mul_one, map_mul]

/-- The integrand for the seed of type `b`: the pullback to the standard line face of `cxP b` of the section. -/
def printedIntegrandB (b : Bool) (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (g : AdelicGL) (u : Adeles × Adeles) : ℂ :=
  (fPull jFace (fun y i j => cxP b (adelicSectionG N n (hfun f) (weyl⁻¹ * lineUnipotent u.1 u.2 * g) y i j)) x p q).coeff m

theorem printedIntegrandB_eq (b : Bool) (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (g : AdelicGL) (u : Adeles × Adeles) :
    printedIntegrandB N n f b x p q m g u = cx b (printedIntegrand N n f x p q m g u) := by
  unfold printedIntegrandB printedIntegrand
  rw [fPull_cxP, coeff_cxP]

theorem printedIntegrand_adelicOf (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (u : Adeles × Adeles) :
    printedIntegrand N n f x p q m (adelicOf (kInvFin k)) u = FzK N k n f x p q m (radicalEquiv u) := by
  unfold printedIntegrand FzK adelicSectionG
  rw [realMatOf_unip_adelicOf, finiteGroup_unip_adelicOf]
  rfl

theorem lineA1K_conj (b : Bool) (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    lineA1K N k n f b x p q m = cx b (lineA1K N k n f false x p q m) := by
  unfold lineA1K
  have h1 : ∀ o : FreeOrbK N k, ∫ v : Fin 2 → ℝ, cxL b (PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v)) =
      cxL b (∫ v : Fin 2 → ℝ, PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v)) := fun o =>
    (cxL b).toContinuousLinearEquiv.integral_comp_comm _
  have h0 : ∀ o : FreeOrbK N k, ∫ v : Fin 2 → ℝ, cxL false (PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v)) =
      ∫ v : Fin 2 → ℝ, PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v) := fun o => by simp [cxL]
  show ∑' o : FreeOrbK N k, _ = cx b (∑' o : FreeOrbK N k, _)
  simp_rw [h1, h0]
  rw [← cxL_apply]
  exact ((cxL b).toContinuousLinearEquiv.map_tsum).symm

/-- **The printed intertwiner at the cusp `k`, both seed types.** For `3 ≤ N`, `4 ≤ n`: absolutely convergent, and equal to
`lineA1K N k n f b`. -/
theorem printed_intertwiner_evalK (hN : 3 ≤ N) (hn : 4 ≤ n) (b : Bool) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    Integrable (printedIntegrandB N n f b x p q m (adelicOf (kInvFin k))) radicalMeasure ∧
    ∫ u, printedIntegrandB N n f b x p q m (adelicOf (kInvFin k)) u ∂radicalMeasure = lineA1K N k n f b x p q m := by
  obtain ⟨hI, hE⟩ := FzK_integral N k n f hN hn hx p q m
  have e : printedIntegrand N n f x p q m (adelicOf (kInvFin k)) =
      fun u => FzK N k n f x p q m (radicalEquiv u) := funext (printedIntegrand_adelicOf N k n f x p q m)
  have hInt : Integrable (printedIntegrand N n f x p q m (adelicOf (kInvFin k))) radicalMeasure := by
    rw [e]; exact (radical_integrable_iff (FzK N k n f x p q m)).2 hI
  have hVal : ∫ u, printedIntegrand N n f x p q m (adelicOf (kInvFin k)) u ∂radicalMeasure =
      lineA1K N k n f false x p q m := by
    rw [e, radical_integral_eq (FzK N k n f x p q m), hE]
    unfold lineA1K
    refine tsum_congr fun o => ?_
    simp [cxL, phiOK, orbCosetK]
  have eB : printedIntegrandB N n f b x p q m (adelicOf (kInvFin k)) =
      fun u => cx b (printedIntegrand N n f x p q m (adelicOf (kInvFin k)) u) :=
    funext fun u => printedIntegrandB_eq N n f b x p q m _ u
  rw [eB]
  refine ⟨?_, ?_⟩
  · have := ((cxL b).toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hInt
    simpa [cxL_apply] using this
  · have := (cxL b).toContinuousLinearEquiv.integral_comp_comm (fun u => printedIntegrand N n f x p q m (adelicOf (kInvFin k)) u) (μ := radicalMeasure)
    simp [cxL_apply] at this
    rw [this, hVal, lineA1K_conj N k n f b]

/-- **Right `K(N)`-invariance of `Tφ(g)` in `g`.** -/
theorem printedIntegrand_adelicOf_ker (hN : 3 ≤ N) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    (gf : FiniteGL) {κ : GL3 IntegralAdeles} (hκ : κ ∈ levelKernel N 3) (u : Adeles × Adeles) :
    printedIntegrand N n f x p q m (adelicOf (gf * GeneralLinearGroup.map integralEmbedding κ)) u =
      printedIntegrand N n f x p q m (adelicOf gf) u := by
  have hy : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  unfold printedIntegrand adelicSectionG
  refine congrArg (fun F => F.coeff m) (fPull_congr_at jFace _ _ x (fun a' b' => ?_) p q)
  rw [realMatOf_unip_adelicOf, realMatOf_unip_adelicOf, finiteGroup_unip_adelicOf, finiteGroup_unip_adelicOf,
    ← mul_assoc]
  exact adelicSection_mul_ker N hN n f (gReal_det _) _ hκ hy a' b'

/-- **The line row of the classical series at every pair of plane cusps `(h, h')` and both seed types, with the literal printed
integrals.** The named `Tξ` of `seriesLineCusp` is the transport of the class of `printedForm` for `k = h' h⁻¹`, whose coordinates are
the absolutely convergent integrals `∫_{𝔸²} φ^b(w₀⁻¹u(s,t) g)`, `g = (1, ι(k⁻¹))`. -/
theorem rLine_series_integralK (hN : 3 ≤ N) (hn : 4 ≤ n) (h h' : SL(3, ℤ)) (b : Bool) :
    lineFaceCuspidalEmbedding N h n (seriesLineCusp N n hN hn f h h' b) =
      (groupCohomology.map (lineAtHom N h) (lineAtMor N h n) 2).hom
        (cxGen (rhoQ N n) (rhoQC N n) (fun _ _ => rfl)
          (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action (rhoQ N n)
            (printedForm N n f hn b (h' * h⁻¹)))) ∧
    ∀ x ∈ faceSet, ∀ (p q : Fin 4) (m : Fin 3 →₀ ℕ),
      Integrable (printedIntegrandB N n f b x p q m (adelicOf (kInvFin (h' * h⁻¹)))) radicalMeasure ∧
      printedCoeff N n f hn b (h' * h⁻¹) x p q m =
        ∫ u, printedIntegrandB N n f b x p q m (adelicOf (kInvFin (h' * h⁻¹))) u ∂radicalMeasure := by
  refine ⟨seriesLineCusp_printed N n f hN hn h h' b, fun x hx p q m => ⟨(printed_intertwiner_evalK N _ n f hN hn b hx p q m).1, ?_⟩⟩
  rw [(printed_intertwiner_evalK N _ n f hN hn b hx p q m).2]
  exact lineAvgK_coeff N _ n f b hn hx p q m

end TernaryPeriodPolynomials.Argument.FormClassK
