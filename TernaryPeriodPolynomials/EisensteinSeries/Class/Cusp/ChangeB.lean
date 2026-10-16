module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KSeries
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.ChangeA
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinClass

@[expose] public section


open scoped MatrixGroups
open ComplexConjugate
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open MvPolynomial
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c

/-!
# Change of the cusp representative: `q h γ` versus `h` (`q ∈ P(ℤ)`, `γ ∈ Γ(N)`)

Formalized by Claude Sonnet 5.5.
Right translation by `Γ(N)` does not change the series (`seriesFormK_false_right`, from the cusp composition law and equivariance); left translation by `q ∈ P(ℤ)` transforms the
cusp form (`exists_cuspChange_full`).  `exists_cuspChange_class`: the real classes of the series at the cusps `q h γ` and `h` agree, after the seed type is changed by `s` and the
cusp form by `φ`.  This is the representative independence needed to compare the face representatives `LineFaces.rep` and `ȷ(planeFaceRepr)`.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

section Compose

open UpperHalfPlane ModularForm

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

omit [NeZero N] in
theorem rho_inv_rho_sl (g : SL(3, ℤ)) (P : MvPolynomial (Fin 3) ℂ) :
    rho (realMat g⁻¹) (rho (realMat g) P) = P := by
  rw [ConvergenceC4.rho_mul, ← realMat_mul, inv_mul_cancel, realMat_one, ConvergenceC4.rho_one]

omit [NeZero N] in
theorem rho_rho_inv_sl (g : SL(3, ℤ)) (P : MvPolynomial (Fin 3) ℂ) :
    rho (realMat g) (rho (realMat g⁻¹) P) = P := by
  simpa using rho_inv_rho_sl g⁻¹ P

omit [NeZero N] in
theorem rho_rho_inv_real {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.det = 1) (P : MvPolynomial (Fin 3) ℂ) :
    rho G (rho G⁻¹ P) = P := by
  rw [ConvergenceC4.rho_mul, Matrix.mul_nonsing_inv _ (by rw [hG]; exact isUnit_one), ConvergenceC4.rho_one]

omit [NeZero N] in
theorem rho_inv_rho_real {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : G.det = 1) (P : MvPolynomial (Fin 3) ℂ) :
    rho G⁻¹ (rho G P) = P := by
  rw [ConvergenceC4.rho_mul, Matrix.nonsing_inv_mul _ (by rw [hG]; exact isUnit_one), ConvergenceC4.rho_one]

/-- **Right translation by `Γ(N)` does not change the series at a cusp** (holomorphic seed, on `Ω`). -/
theorem seriesFormK_false_right (hn : 4 ≤ n) (h' : SL(3, ℤ)) {γ : SL(3, ℤ)} (hγ : γ ∈ gammaN N)
    {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a c : Fin 5) :
    seriesFormK false (CuspData.ofSL (h' * γ)) (gammaN N) n f y a c =
      seriesFormK false (CuspData.ofSL h') (gammaN N) n f y a c := by
  have comp := seriesFormK_false_comp N n f hn γ⁻¹ h' hy a c
  have eqv := seriesFormK_pullback false (CuspData.ofSL h') (gammaN N) (leviGroup N) n f hn
    (leviInCusp_gammaN N h') ⟨γ, hγ⟩ hy a c
  rw [inv_inv] at comp
  have e1 : rho (realMat γ) (seriesFormK false (CuspData.ofSL (h' * γ)) (gammaN N) n f y a c) =
      rho (realMat γ) (seriesFormK false (CuspData.ofSL h') (gammaN N) n f y a c) := by
    rw [← comp]
    exact eqv
  have := congrArg (rho (realMat γ⁻¹)) e1
  rwa [rho_inv_rho_sl, rho_inv_rho_sl] at this




/-- **Left translation by `q ∈ P(ℤ)` and right translation by `Γ(N)`**: the series (holomorphic seed) at the cusp `q h γ` is the (possibly conjugated) series at the cusp `h`
of the transformed cusp form `φ f`, on `Ω`. -/
theorem exists_cuspChange_full (hn : 4 ≤ n) {q : SL(3, ℤ)} (hq : q ∈ planeBorel) :
    ∃ (s : Bool) (φ : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ) → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)),
      ∀ (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h γ : SL(3, ℤ)), γ ∈ gammaN N →
        ∀ {y : Fin 5 → ℝ}, y ∈ Omega → ∀ a c : Fin 5,
        seriesFormK false (CuspData.ofSL (q * h * γ)) (gammaN N) n f y a c =
          cxP s (seriesFormK false (CuspData.ofSL h) (gammaN N) n (φ f) y a c) := by
  obtain ⟨s, φ, hφ⟩ := exists_cuspChange N n hq
  refine ⟨s, φ, fun f h γ hγ y hy a c => ?_⟩
  rw [seriesFormK_false_right N n f hn (q * h) hγ hy a c, seriesFormK_false_eq N n f hn (q * h) hy a c,
    seriesFormK_false_eq N n (φ f) hn h hy a c]
  have hΦ : planeAct (realMat h) y ∈ Omega := planeAct_mem (det_realMat h) hy
  have hd1 : DifferentiableAt ℝ (planeAct (realMat h)) y := differentiableAt_planeAct (det_realMat h) hy
  have hd2 : DifferentiableAt ℝ (planeAct (realMat q)) (planeAct (realMat h) y) :=
    differentiableAt_planeAct (det_realMat q) hΦ
  have hev : planeAct (realMat (q * h)) =ᶠ[nhds y] (planeAct (realMat q) ∘ planeAct (realMat h)) :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hy) fun z hz => by
      rw [realMat_mul]
      exact planeAct_mul (det_realMat h) hz
  rw [formPullback_congr _ hev, formPullback_comp _ _ _ y hd1 hd2 a c]
  have hq1 : ∀ a' c', formPullback (planeAct (realMat q)) (seriesForm (gammaN N) n f) (planeAct (realMat h) y) a' c' =
      rho (realMat q) (cxP s (seriesForm (gammaN N) n (φ f) (planeAct (realMat h) y) a' c')) := by
    intro a' c'
    rw [← hφ f hΦ a' c', seriesFormK_false_eq N n f hn q hΦ a' c', rho_rho_inv_real (det_realMat q)]
  have hin : formPullback (planeAct (realMat h)) (formPullback (planeAct (realMat q)) (seriesForm (gammaN N) n f)) y a c =
      formPullback (planeAct (realMat h)) (fun z a' c' => rho (realMat q) (cxP s (seriesForm (gammaN N) n (φ f) z a' c')))
        y a c :=
    formPullback_congr_form y (fun a' c' => hq1 a' c') a c
  rw [hin, EisensteinClass.formPullback_rho (realMat q) (planeAct (realMat h))
    (fun z a' c' => cxP s (seriesForm (gammaN N) n (φ f) z a' c')) y a c,
    formPullback_cxP s (planeAct (realMat h)) (seriesForm (gammaN N) n (φ f)) y a c, realMat_mul,
    Matrix.mul_inv_rev, ← ConvergenceC4.rho_mul, rho_inv_rho_real (det_realMat q), rho_cxP]




omit [NeZero N] in
theorem cxP_cxP (b s : Bool) (q : MvPolynomial (Fin 3) ℂ) : cxP b (cxP s q) = cxP (xor b s) q := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_cxP, coeff_cxP, coeff_cxP]
  cases b <;> cases s <;> simp [cx]

omit [NeZero N] in
theorem InvComponents_toInv_congr {Γ : Subgroup SL(3, ℤ)} {n : ℕ} {W W' : InvComponents Γ n}
    (h : ∀ y ∈ Omega, ∀ a b, W.comp y a b = W'.comp y a b) : W.toInv = W'.toInv := by
  refine Subtype.ext ?_
  apply Form.ext
  intro x hx
  change (W.form : RawForm (Fin 5 → ℝ) (Coef n) 2) x = (W'.form : RawForm (Fin 5 → ℝ) (Coef n) 2) x
  rw [W.form_apply hx, W'.form_apply hx]
  unfold InvComponents.raw
  congr 1
  funext a b
  exact h x hx a b

/-- **The class of the series at the cusp `q h γ`** (`q ∈ P(ℤ)`, `γ ∈ Γ(N)`) is the class of the series at the cusp `h`, with the seed type changed by `s` and
the cusp form by `φ` (the Levi slash, followed by `f ↦ f^*` if `s = true`). -/
theorem exists_cuspChange_class (hn : 4 ≤ n) {q : SL(3, ℤ)} (hq : q ∈ planeBorel) :
    ∃ (s : Bool) (φ : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ) → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)),
      ∀ (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h γ : SL(3, ℤ)), γ ∈ gammaN N → ∀ b : Bool,
        Statements.EisensteinClass.eisensteinAtClass_gammaN N n f (q * h * γ) b hn =
          Statements.EisensteinClass.eisensteinAtClass_gammaN N n (φ f) h (xor b s) hn := by
  obtain ⟨s, φ, hφ⟩ := exists_cuspChange_full N n hn hq
  refine ⟨s, φ, fun f h γ hγ b => ?_⟩
  have hW : (Statements.EisensteinClass.planeEisensteinAtComponents b (CuspData.ofSL (q * h * γ)) (gammaN N)
      (leviGroup N) n f hn (leviInCusp_gammaN N (q * h * γ))).toInv =
      (Statements.EisensteinClass.planeEisensteinAtComponents (xor b s) (CuspData.ofSL h) (gammaN N)
      (leviGroup N) n (φ f) hn (leviInCusp_gammaN N h)).toInv := by
    refine InvComponents_toInv_congr (fun y hy a c => ?_)
    change Coef.mk (Statements.ConvergenceC4.planeEisensteinAt b (CuspData.ofSL (q * h * γ)) (gammaN N) n f y a c) =
      Coef.mk (Statements.ConvergenceC4.planeEisensteinAt (xor b s) (CuspData.ofSL h) (gammaN N) n (φ f) y a c)
    congr 1
    refine Subtype.ext ?_
    change seriesFormK b (CuspData.ofSL (q * h * γ)) (gammaN N) n f y a c =
      seriesFormK (xor b s) (CuspData.ofSL h) (gammaN N) n (φ f) y a c
    rw [seriesFormK_cxP _ _ n N f b, hφ f h γ hγ hy a c, cxP_cxP, seriesFormK_cxP _ _ n N (φ f) (xor b s)]
  exact congrArg (ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct (gammaN N))
    (gammaRho (gammaN N) n)) hW

end Compose

end TernaryPeriodPolynomials.Argument.EisensteinClass
