module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KAnalysis
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.UnfoldLin
public import TernaryPeriodPolynomials.EisensteinSeries.Class.IterComm
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Linearity

@[expose] public section


/-!
# The radical average of the series of either seed type at the cusp `k⁻¹ P k` on the line face

With "the same letters for the rational conjugates".

`lineAvgK_coeff`: for every `k ∈ SL₃(ℤ)`, seed type `b` and `4 ≤ n`, the `m`-th coefficient of the radical
average `(lineTwist N n).avInvT (lineFaceForm N n 𝓔^b_{k})` at `(x; e_p, e_q)` is `lineA1K`, the sum over
the free orbits of the line radical lattice on `Γ_{k⁻¹Pk}\Γ(N)` (the cosets with `(k γ)₂₀ ≠ 0`) of the `ℝ²`
integral of `cxL b (PhiQ0)` at the orbit representative. The cosets with `(k γ)₂₀ = 0` contribute zero
(cuspidality). `lineA1K` is absolutely summable, additive in `f`, and homogeneous with the scalar `cx b a`
(`ℂ`-linear for `b = false`, conjugate-linear for `b = true`). For `k = 1`, `b = false` it is the
function `lineA1` of `LineUnfoldLin`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set MvPolynomial
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.GammaNFaces
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinDual
  TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
  TernaryPeriodPolynomials.Argument.SeedC3.Psi

section Big

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

theorem cxL_intervalIntegral (b : Bool) (g : ℝ → ℂ) :
    ∫ s in (0 : ℝ)..1, cxL b (g s) = cxL b (∫ s in (0 : ℝ)..1, g s) := by
  cases b
  · simp [cxL]
  · simp only [cxL, ite_true]
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    exact integral_conj

/-- The explicit coefficient of the radical average of the series of type `b` at the cusp `k⁻¹Pk`:
the sum over the free orbits of the `ℝ²` integrals of the orbit representatives. -/
def lineA1K (b : Bool) (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) : ℂ :=
  ∑' o : {o : Quotient (qActK N k).orbSetoid // (qActK N k).r0Q o ≠ 0},
    ∫ v : Fin 2 → ℝ, cxL b (PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v))

theorem PhiQK_data (b : Bool) (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    (∀ ℓ c w, cxL b (PhiQ0 N k n f x p q m ((qActK N k).act ℓ c) w) =
      cxL b (PhiQ0 N k n f x p q m c ((N : ℝ) • intVec ℓ + w))) ∧
    (∀ c, Continuous fun w => cxL b (PhiQ0 N k n f x p q m c w)) ∧
    (∀ R : ℝ, ∃ B : Ck N k → ℝ, Summable B ∧ ∀ c w, (∀ i, |w i| ≤ R) →
      ‖cxL b (PhiQ0 N k n f x p q m c w)‖ ≤ B c) := by
  obtain ⟨hc, hb⟩ := PhiQ0_continuous_bound N k n f hn hx p q m
  refine ⟨fun ℓ c w => ?_, fun c => (cxL b).continuous.comp (hc c), fun R => ?_⟩
  · exact congrArg (cxL b) (PhiQ0_latQ N k n f hx p q m ℓ c w)
  · obtain ⟨B, hBs, hBb⟩ := hb R
    exact ⟨B, hBs, fun c w hw => by rw [LinearIsometryEquiv.norm_map]; exact hBb c w hw⟩

theorem lineAvgK_coeff (b : Bool) (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    (Coef.toPoly (((((lineTwist N n).avInvT
        (lineFaceForm N n (planeEisensteinAtInv b (CuspData.ofSL k) (gammaN N) (leviGroup N) n f hn
          (leviInCusp_gammaN N k))) :
          ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action (rhoQ N n)) :
            Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
          ![Pi.single p 1, Pi.single q 1])).coeff m = lineA1K N k n f b x p q m := by
  set W := (lineFaceForm N n (planeEisensteinAtInv b (CuspData.ofSL k) (gammaN N) (leviGroup N) n f hn
    (leviInCusp_gammaN N k))).1 with hW
  have hcontOn := contDiffOn_avIntegrandS (n := n) (k := 2) (lineTwist N n).uni.smooth (N : ℝ) W
  have hcont : Continuous (Function.uncurry fun a b : ℝ =>
      avIntegrandS 2 (lineTwist N n).σ (N : ℝ) W ((x, a), b)) := by
    have : Continuous fun p : ℝ × ℝ => ((x, p.1), p.2) := by fun_prop
    exact hcontOn.continuousOn.comp_continuous this fun p => ⟨⟨hx, mem_univ _⟩, mem_univ _⟩
  change (Coef.toPoly (((avFormS (lineTwist N n).uni.smooth (N : ℝ) W : Form (F := Coef n) faceSet 2) :
    RawForm Face (Coef n) 2) x ![Pi.single p 1, Pi.single q 1])).coeff m = _
  rw [avFormS_apply _ _ _ hx]
  unfold avRawS
  set Λ : (Face [⋀^Fin 2]→L[ℝ] Coef n) →L[ℝ] ℂ :=
    (polyCoefCLM n m).comp (evalPairCLM n (Pi.single p 1) (Pi.single q 1)) with hΛ
  have h1 := iterIntegral_clm_comm Λ (fun a b => avIntegrandS 2 (lineTwist N n).σ (N : ℝ) W ((x, a), b))
    hcont
  have h2 : Λ (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
      avIntegrandS 2 (lineTwist N n).σ (N : ℝ) W ((x, a), b)) =
      (Coef.toPoly ((∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1,
        avIntegrandS 2 (lineTwist N n).σ (N : ℝ) W ((x, a), b)) ![Pi.single p 1, Pi.single q 1])).coeff m :=
    rfl
  have h3 : ∀ a b' : ℝ, Λ (avIntegrandS 2 (lineTwist N n).σ (N : ℝ) W ((x, a), b')) =
      ∑' c : Ck N k, cxL b (PhiQ0 N k n f x p q m c ((N : ℝ) • ![a, b'])) := by
    intro a b'
    rw [← coeff_avIntegrandK N k n f b hn hx ((N : ℝ) • ![a, b']) p q m]
    show polyCoefCLM n m (evalPairCLM n (Pi.single p 1) (Pi.single q 1)
      (((shiftS 2 (lineTwist N n).σ ((N : ℝ) • ![a, b']) W : Form (F := Coef n) faceSet 2) :
        RawForm Face (Coef n) 2) x)) = _
    rw [shiftS_apply 2 _ _ W hx]
    rfl
  rw [← h2, h1]
  simp only [h3]
  obtain ⟨hE, hC, hB⟩ := PhiQK_data N k n f b hn hx p q m
  refine QAct.total (qActK N k) (fun c w => cxL b (PhiQ0 N k n f x p q m c w)) hE hC hB ?_
  intro c hc0
  obtain ⟨i, hi⟩ := PhiQ0_closed N k n f hx p q m c hc0
  refine ⟨i, fun w => ?_⟩
  rw [cxL_intervalIntegral, hi w]
  simp

end Big

section Linearity

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ)

/-- The `f`-independent kernel of the integrand: `Σ_{a,b} ∂_pΦ_a ∂_qΦ_b K_{ab}(k γ_c qMat v, jFace x)`. -/
def KQK (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (c : Ck N k) (v : Fin 2 → ℝ) : ℂ :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    ((((fderiv ℝ jFace x (Pi.single p 1) a * fderiv ℝ jFace x (Pi.single q 1) b : ℝ) : ℂ))) *
      Kfun n (realMat (k * (Quotient.out c).1) * qMat v) (jFace x) a b m

omit [NeZero N] in
/-- **The integrand is the seed at the image point times a kernel** (the real form of the intertwining
integrand): `PhiQ0 c v = h(τ(k γ_c qMat v · y₀)) · KQK`, where `h = f ∘ ofComplex`, `y₀ = jFace x` and
`KQK` does not depend on `f`. -/
theorem PhiQ0_eq_seed_mul_kernel (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) {x : Face}
    (p q : Fin 4) (m : Fin 3 →₀ ℕ) (c : Ck N k) (v : Fin 2 → ℝ) :
    PhiQ0 N k n f x p q m c v =
      hfun f (seedTau (planeAct (realMat (k * (Quotient.out c).1) * qMat v) (jFace x))) *
        KQK N k n x p q m c v := by
  have hG : (realMat (k * (Quotient.out c).1) * qMat v).det = 1 := by
    rw [Matrix.det_mul, det_realMat, det_qMat]; norm_num
  rw [PhiQ0_as_sum N k n f p q m c v]
  unfold KQK
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coeff_summandPoly_eq n (hfun f) hG (jFace x) a b m]
  ring

omit [NeZero N] in
theorem PhiQ0_add (f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) {x : Face} (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) (c : Ck N k) (v : Fin 2 → ℝ) :
    PhiQ0 N k n (f + g) x p q m c v = PhiQ0 N k n f x p q m c v + PhiQ0 N k n g x p q m c v := by
  rw [PhiQ0_eq_seed_mul_kernel, PhiQ0_eq_seed_mul_kernel, PhiQ0_eq_seed_mul_kernel,
    hfun_add (leviGroup N) n]
  ring

omit [NeZero N] in
theorem PhiQ0_smul (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (a : ℂ) {x : Face} (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) (c : Ck N k) (v : Fin 2 → ℝ) :
    PhiQ0 N k n (a • f) x p q m c v = a * PhiQ0 N k n f x p q m c v := by
  rw [PhiQ0_eq_seed_mul_kernel, PhiQ0_eq_seed_mul_kernel, hfun_smul (leviGroup N) n]
  ring

theorem lineA1K_data (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (b : Bool) (hn : 4 ≤ n)
    {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    Summable (fun o : {o : Quotient (qActK N k).orbSetoid // (qActK N k).r0Q o ≠ 0} =>
      ∫ v : Fin 2 → ℝ, cxL b (PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v))) ∧
    ∀ o : {o : Quotient (qActK N k).orbSetoid // (qActK N k).r0Q o ≠ 0},
      Integrable (fun v : Fin 2 → ℝ =>
        cxL b (PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v))) := by
  obtain ⟨hE, hC, hB⟩ := PhiQK_data N k n f b hn hx p q m
  exact ⟨QAct.orbit_summable (qActK N k) (fun c w => cxL b (PhiQ0 N k n f x p q m c w)) hE hC hB,
    fun o => QAct.orbit_integrable (qActK N k) (fun c w => cxL b (PhiQ0 N k n f x p q m c w)) hE hC hB
      o.1 o.2⟩

/-- **`lineA1K` is additive in the cusp form.** -/
theorem lineA1K_add (f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (b : Bool) (hn : 4 ≤ n)
    {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    lineA1K N k n (f + g) b x p q m = lineA1K N k n f b x p q m + lineA1K N k n g b x p q m := by
  obtain ⟨hsf, hif⟩ := lineA1K_data N k n f b hn hx p q m
  obtain ⟨hsg, hig⟩ := lineA1K_data N k n g b hn hx p q m
  unfold lineA1K
  rw [← hsf.tsum_add hsg]
  refine tsum_congr fun o => ?_
  have : (fun v : Fin 2 → ℝ => cxL b (PhiQ0 N k n (f + g) x p q m (Quotient.out o.1) ((N : ℝ) • v))) =
      fun v => cxL b (PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v)) +
        cxL b (PhiQ0 N k n g x p q m (Quotient.out o.1) ((N : ℝ) • v)) := by
    funext v
    rw [PhiQ0_add, map_add]
  rw [this]
  exact integral_add (hif o) (hig o)

/-- **`lineA1K` is homogeneous with the scalar `cx b a`**: `ℂ`-linear for the holomorphic seed,
conjugate-linear for the antiholomorphic seed. -/
theorem lineA1K_smul (a : ℂ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (b : Bool) {x : Face}
    (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    lineA1K N k n (a • f) b x p q m = cx b a * lineA1K N k n f b x p q m := by
  unfold lineA1K
  rw [← tsum_mul_left]
  refine tsum_congr fun o => ?_
  have : (fun v : Fin 2 → ℝ => cxL b (PhiQ0 N k n (a • f) x p q m (Quotient.out o.1) ((N : ℝ) • v))) =
      fun v => cx b a * cxL b (PhiQ0 N k n f x p q m (Quotient.out o.1) ((N : ℝ) • v)) := by
    funext v
    rw [PhiQ0_smul, cxL_apply, cxL_apply]
    cases b <;> simp [cx]
  rw [this]
  exact integral_const_mul _ _

end Linearity

end TernaryPeriodPolynomials.Argument.EisensteinClass
