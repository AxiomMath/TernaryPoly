module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.UnfoldAbs
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.UnfoldPhi
public import TernaryPeriodPolynomials.EisensteinSeries.Class.IterComm
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Linearity

@[expose] public section


/-!
# The radical average of the series on the line face: only the free cell survives

The constant term `r_Q 𝓔_P(ξ) = T ξ` (eq. `ar:eq:constantterms`).

`lineAvg_coeff`: for `3 ≤ N`-free statement with `4 ≤ n`, the `m`-th coefficient of the radical average
`(lineTwist N n).avInvT (lineFaceForm N n 𝓔)` at `(x; e_p, e_q)` is the sum, over the free orbits of the line
radical lattice acting on `Γ_P \ Γ(N)` (the cosets with `r₀ ≠ 0`, the double coset `Q w₀⁻¹ P`), of the `ℝ²`
integral `∫_{ℝ²} PhiQ(c_O)(N v) dv` of the coefficient of the face pullback of the summand at `γ_{c_O}
qMat v`. The cosets with `r₀ = 0` (the line lies in the plane, row `Q, I`) contribute zero by cuspidality
(`PhiQ_closed`, `QAct.total`).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Set MvPolynomial
open scoped MatrixGroups ContDiff
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

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- **The line radical lattice acting on the cosets `Γ_P \ Γ(N)`**: trivial on the cell `r₀ = 0`, free on
the cell `r₀ ≠ 0`. -/
def qActGamma : QAct N (PlaneCoset (gammaN N)) where
  act ℓ := cosetMulR (gammaN N) (latQ N ℓ)
  r0 c := cosetRow (gammaN N) c 0
  act_zero c := by rw [latQ_zero, cosetMulR_one]
  act_add ℓ ℓ' c := by rw [latQ_add, cosetMulR_mul]
  r0_act ℓ c := (cosetRow_latQ N ℓ c).1
  fix ℓ c h := latQ_fix N ℓ c h
  free c h := latQ_free N c h

end Big

section Coefficients

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- **The line-radical average of the series on the line face, coordinate by coordinate**
(`4 ≤ n`): only the free orbits (`r₀ ≠ 0`) contribute, each through the `ℝ²` integral of its
representative. -/
theorem lineAvg_coeff (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    (Coef.toPoly (((((lineTwist N n).avInvT
        (lineFaceForm N n (planeEisensteinInv (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N))) :
          ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action (rhoQ N n)) :
            Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
          ![Pi.single p 1, Pi.single q 1])).coeff m =
      ∑' o : {o : Quotient (qActGamma N).orbSetoid // (qActGamma N).r0Q o ≠ 0},
        ∫ v : Fin 2 → ℝ, PhiQ N n f x p q m (Quotient.out o.1) ((N : ℝ) • v) := by
  set W := (lineFaceForm N n (planeEisensteinInv (gammaN N) (leviGroup N) n f hn
    (leviIn_gammaN N))).1 with hW
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
  have h3 : ∀ a b : ℝ, Λ (avIntegrandS 2 (lineTwist N n).σ (N : ℝ) W ((x, a), b)) =
      ∑' c : PlaneCoset (gammaN N), PhiQ N n f x p q m c ((N : ℝ) • ![a, b]) := by
    intro a b
    rw [← coeff_avIntegrand N n f hn hx ((N : ℝ) • ![a, b]) p q m]
    show polyCoefCLM n m (evalPairCLM n (Pi.single p 1) (Pi.single q 1)
      (((shiftS 2 (lineTwist N n).σ ((N : ℝ) • ![a, b]) W : Form (F := Coef n) faceSet 2) :
        RawForm Face (Coef n) 2) x)) = _
    rw [shiftS_apply 2 _ _ W hx]
    rfl
  rw [← h2, h1]
  simp only [h3]
  exact QAct.total (qActGamma N) (fun c w => PhiQ N n f x p q m c w)
    (fun ℓ c w => PhiQ_latQ hx p q m ℓ c w)
    (fun c => (PhiQ_continuous_bound N n f hn hx p q m).1 c)
    (fun R => (PhiQ_continuous_bound N n f hn hx p q m).2 R)
    (fun c hc => PhiQ_closed N n f hx p q m c hc)

end Coefficients

section Integrand

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The `h`-independent kernel of the integrand of the line-radical average:
`Σ_{a,b} ∂_pΦ_a ∂_qΦ_b K_{ab}(γ qMat v, jFace x)`. -/
def KQ (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) (c : PlaneCoset (gammaN N)) (v : Fin 2 → ℝ) : ℂ :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    ((((fderiv ℝ jFace x (Pi.single p 1) a * fderiv ℝ jFace x (Pi.single q 1) b : ℝ) : ℂ))) *
      Kfun n (realMat (Quotient.out c).1 * qMat v) (jFace x) a b m

omit [NeZero N] in
/-- **The integrand is the seed at the image point times a kernel** (the real form of the intertwining
integrand `φ(w₀⁻¹ u(s,t) g)`): `PhiQ c v = h(τ(γ_c qMat v · y₀)) · K`, where `h = f ∘ ofComplex`,
`y₀ = jFace x`, `τ` the upper-half-plane coordinate of the plane point and `K = KQ` does not depend on
`f`. -/
theorem PhiQ_eq_seed_mul_kernel {x : Face} (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    (c : PlaneCoset (gammaN N)) (v : Fin 2 → ℝ) :
    PhiQ N n f x p q m c v =
      hfun f (seedTau (planeAct (realMat (Quotient.out c).1 * qMat v) (jFace x))) *
        KQ N n x p q m c v := by
  have hG : (realMat (Quotient.out c).1 * qMat v).det = 1 := by
    rw [Matrix.det_mul, det_realMat, det_qMat]; norm_num
  rw [PhiQ_as_sum N n f p q m c v]
  unfold KQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coeff_summandPoly_eq n (hfun f) hG (jFace x) a b m]
  ring

omit [NeZero N] in
/-- `PhiQ` is additive in the cusp form. -/
theorem PhiQ_add (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) {x : Face} (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) (c : PlaneCoset (gammaN N)) (v : Fin 2 → ℝ) :
    PhiQ N n (f + g) x p q m c v = PhiQ N n f x p q m c v + PhiQ N n g x p q m c v := by
  rw [PhiQ_eq_seed_mul_kernel, PhiQ_eq_seed_mul_kernel, PhiQ_eq_seed_mul_kernel, hfun_add (leviGroup N) n]
  ring

omit [NeZero N] in
/-- `PhiQ` is homogeneous in the cusp form. -/
theorem PhiQ_smul (a : ℂ) {x : Face} (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) (c : PlaneCoset (gammaN N)) (v : Fin 2 → ℝ) :
    PhiQ N n (a • f) x p q m c v = a * PhiQ N n f x p q m c v := by
  rw [PhiQ_eq_seed_mul_kernel, PhiQ_eq_seed_mul_kernel, hfun_smul (leviGroup N) n]
  ring

end Integrand

end TernaryPeriodPolynomials.Argument.EisensteinClass
