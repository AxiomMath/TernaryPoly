module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Convergence
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Compact
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Smooth
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

@[expose] public section


/-!
# Smooth dependence on the compact parameter, and uniform jets (Appendix C.3)

Uniform bounds of iterated derivatives over a compact parameter set; the coefficients of powers of
a linear form are polynomial; the universal family `Ψ(k,q,x) = Φ_k Φ_{P(q)⁻¹} x` and the coordinate
functions of the formula are jointly smooth.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

/-! ### Uniform bounds of iterated derivatives over a compact parameter set -/

theorem exists_bound_iteratedFDeriv_family :
    ∀ (N : ℕ) {P E F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E]
      [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (V : P → E → F)
      (W : Set (P × E)), IsCompact W →
      (∀ w ∈ W, ContDiffAt ℝ ∞ (fun p : P × E => V p.1 p.2) w) →
      ∃ C : ℝ, ∀ w ∈ W, ‖iteratedFDeriv ℝ N (V w.1) w.2‖ ≤ C := by
  intro N
  induction N with
  | zero =>
    intro P E F _ _ _ _ _ _ V W hW hV
    obtain ⟨C, hC⟩ := hW.exists_bound_of_continuousOn
      (f := fun w : P × E => V w.1 w.2) (fun w hw => (hV w hw).continuousAt.continuousWithinAt)
    exact ⟨C, fun w hw => by simpa using hC w hw⟩
  | succ N ih =>
    intro P E F _ _ _ _ _ _ V W hW hV
    have hV' : ∀ w ∈ W, ContDiffAt ℝ ∞ (fun p : P × E => fderiv ℝ (V p.1) p.2) w := by
      intro w hw
      have h1 : ContDiffAt ℝ ∞ (Function.uncurry fun (e : P × E) (y : E) => V e.1 y) (w, w.2) := by
        have := (hV w hw).comp (w, w.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
        exact this
      exact h1.fderiv (g := fun e : P × E => e.2) contDiffAt_snd (m := ∞) (by simp)
    obtain ⟨C, hC⟩ := ih (fun p x => fderiv ℝ (V p) x) W hW hV'
    refine ⟨C, fun w hw => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv]
    exact hC w hw

/-! ### The coefficients of a power of a linear form are polynomial in its coefficients -/

/-- The `m`-th coefficient of `(c₀ X + c₁ Y + c₂ Z)^n`, as a function of `c`. -/
def polyCoeff (n : ℕ) (m : Fin 3 →₀ ℕ) (c : Fin 3 → ℂ) : ℂ :=
  ((∑ l : Fin 3, C (c l) * X l : MvPolynomial (Fin 3) ℂ) ^ n).coeff m

theorem polyCoeff_succ (n : ℕ) (m : Fin 3 →₀ ℕ) (c : Fin 3 → ℂ) :
    polyCoeff (n + 1) m c =
      ∑ l : Fin 3, c l * (if l ∈ m.support then polyCoeff n (m - Finsupp.single l 1) c else 0) := by
  unfold polyCoeff
  rw [pow_succ, Finset.mul_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (∑ l : Fin 3, C (c l) * X l : MvPolynomial (Fin 3) ℂ) ^ n * (C (c l) * X l) =
      C (c l) * ((∑ l : Fin 3, C (c l) * X l : MvPolynomial (Fin 3) ℂ) ^ n * X l) by ring,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']

theorem contDiff_polyCoeff (n : ℕ) : ∀ (m : Fin 3 →₀ ℕ), ContDiff ℝ ∞ (polyCoeff n m) := by
  induction n with
  | zero =>
    intro m
    have : polyCoeff 0 m = fun _ => (1 : MvPolynomial (Fin 3) ℂ).coeff m := by
      funext c; simp [polyCoeff]
    rw [this]; exact contDiff_const
  | succ n ih =>
    intro m
    have : polyCoeff (n + 1) m = fun c => ∑ l : Fin 3, c l *
        (if l ∈ m.support then polyCoeff n (m - Finsupp.single l 1) c else 0) := by
      funext c; exact polyCoeff_succ n m c
    rw [this]
    refine ContDiff.sum fun l _ => ?_
    refine (contDiff_apply ℝ ℂ l).mul ?_
    by_cases hl : l ∈ m.support
    · simpa [hl] using ih (m - Finsupp.single l 1)
    · simpa [hl] using contDiff_const

theorem coeff_linear_pow (n : ℕ) (m : Fin 3 →₀ ℕ) (s : ℂ) (c : Fin 3 → ℂ) :
    (C s * (∑ l : Fin 3, C (c l) * X l : MvPolynomial (Fin 3) ℂ) ^ n).coeff m =
      s * polyCoeff n m c := by
  rw [MvPolynomial.coeff_C_mul]; rfl

/-! ### The universal family `Ψ(k,q,x) = Φ_k (Φ_{P(q)⁻¹} x)` -/

/-- Parameters `(k, q)`. -/
abbrev Par := (Fin 3 → Fin 3 → ℝ) × (Fin 5 → ℝ)

/-- The universal map `R_{k,q} = Φ_k ∘ Φ_{P(q)⁻¹}`. -/
def Psi (z : Par) (x : Fin 5 → ℝ) : Fin 5 → ℝ :=
  planeAct (matOfFun z.1) (planeAct (planePinv z.2) x)

theorem decompR_eq_Psi (g : Matrix (Fin 3) (Fin 3) ℝ) (q : Fin 5 → ℝ) :
    decompR g q = Psi (matToFun (kFactor g q), q) := rfl

theorem contDiffAt_inner {z : Par} (hq : z.2 ∈ Omega) {x : Fin 5 → ℝ} (hx : x ∈ Omega) :
    ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => planeAct (planePinv p.1.2) p.2) (z, x) := by
  have hin : ContDiffAt ℝ ⊤ (fun p : Par × (Fin 5 → ℝ) =>
      (matToFun (planePinv p.1.2), p.2)) (z, x) :=
    ((contDiffAt_matToFun_planePinv hq).comp (z, x) (contDiffAt_snd.comp (z, x) contDiffAt_fst)).prodMk
      contDiffAt_snd
  have := (contDiffAt_planeAct_pair (g := planePinv z.2) (det_planePinv hq) hx).comp (z, x) hin
  exact this.of_le (by exact_mod_cast le_top)

theorem contDiffAt_Psi {z : Par} (hk : (matOfFun z.1).det = 1) (hq : z.2 ∈ Omega)
    {x : Fin 5 → ℝ} (hx : x ∈ Omega) :
    ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => Psi p.1 p.2) (z, x) := by
  have hy : planeAct (planePinv z.2) x ∈ Omega := planeAct_mem (det_planePinv hq) hx
  have hin : ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) =>
      (p.1.1, planeAct (planePinv p.1.2) p.2)) (z, x) :=
    (contDiffAt_fst.comp (z, x) contDiffAt_fst).prodMk (contDiffAt_inner hq hx)
  have h2 := (contDiffAt_planeAct_pair (g := matOfFun z.1) hk hy)
  have := (h2.of_le (by exact_mod_cast le_top : (∞ : WithTop ℕ∞) ≤ ⊤)).comp (z, x) hin
  exact this

/-! ### The scalar `θ` and the coordinate functions of the formula -/

/-- The coefficient of `h_A(τ(R x))` in the scalar pullback of `h_A β ∧ dτ` by `R`. -/
def theta (R : (Fin 5 → ℝ) → (Fin 5 → ℝ)) (x : Fin 5 → ℝ) (i j : Fin 5) : ℂ :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    ((fderiv ℝ R x (Pi.single i 1) a * fderiv ℝ R x (Pi.single j 1) b : ℝ) : ℂ) *
      (seedBeta (R x) a * seedDTau b - seedBeta (R x) b * seedDTau a)

theorem scalarPullback_seedForm0 (φ : ℂ → ℂ) (R : (Fin 5 → ℝ) → (Fin 5 → ℝ)) (x : Fin 5 → ℝ)
    (i j : Fin 5) :
    scalarPullback R (seedForm0 φ) x i j = φ (seedTau (R x)) * theta R x i j := by
  unfold scalarPullback seedForm0 theta
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem contDiff_seedTau : ContDiff ℝ ∞ seedTau := by
  unfold seedTau
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 2)).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 3))))

theorem contDiff_seedBeta_apply (a : Fin 5) : ContDiff ℝ ∞ (fun y => seedBeta y a) := by
  fin_cases a <;> simp [seedBeta] <;> first | exact contDiff_const | exact contDiff_seedTau.neg

theorem contDiff_seedRow_apply (k : Fin 3) : ContDiff ℝ ∞ (fun y => seedRow y k) := by
  fin_cases k <;> simp [seedRow]
  · exact contDiff_const
  · exact contDiff_seedTau
  · exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).sub
      (contDiff_seedTau.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)))

/-- `u₁(z, x) = τ(R_z x)`. -/
def uTau (z : Par) (x : Fin 5 → ℝ) : ℂ := seedTau (Psi z x)

/-- `u₂(z, x) = θ_{ij}(R_z, x)`. -/
def uTheta (i j : Fin 5) (z : Par) (x : Fin 5 → ℝ) : ℂ := theta (Psi z) x i j

/-- `u₃(z, x)`: the coefficients of the transformed linear form. -/
def uRow (z : Par) (x : Fin 5 → ℝ) : Fin 3 → ℂ :=
  fun l => ∑ k : Fin 3, seedRow (Psi z x) k * (((matOfFun z.1 * planePinv z.2) k l : ℝ) : ℂ)

/-- `u₄(z, x) = polyCoeff n m (u₃(z, x))`. -/
def uPoly (n : ℕ) (m : Fin 3 →₀ ℕ) (z : Par) (x : Fin 5 → ℝ) : ℂ := polyCoeff n m (uRow z x)

/-- Admissible parameters: `det k = 1` and `q ∈ Ω`. -/
def GoodPar (z : Par) : Prop := (matOfFun z.1).det = 1 ∧ z.2 ∈ Omega

theorem contDiffAt_fderivPsi {z : Par} (hz : GoodPar z) {x : Fin 5 → ℝ} (hx : x ∈ Omega) :
    ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => fderiv ℝ (Psi p.1) p.2) (z, x) := by
  have h1 : ContDiffAt ℝ ∞ (Function.uncurry fun (e : Par × (Fin 5 → ℝ)) (y : Fin 5 → ℝ) =>
      Psi e.1 y) ((z, x), x) := by
    have := (contDiffAt_Psi hz.1 hz.2 hx).comp ((z, x), x)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact this
  exact h1.fderiv (g := fun e : Par × (Fin 5 → ℝ) => e.2) contDiffAt_snd (m := ∞) (by simp)

theorem contDiffAt_uTau {z : Par} (hz : GoodPar z) {x : Fin 5 → ℝ} (hx : x ∈ Omega) :
    ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => uTau p.1 p.2) (z, x) :=
  contDiff_seedTau.contDiffAt.comp (z, x) (contDiffAt_Psi hz.1 hz.2 hx)

theorem contDiffAt_uRow {z : Par} (hz : GoodPar z) {x : Fin 5 → ℝ} (hx : x ∈ Omega) :
    ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => uRow p.1 p.2) (z, x) := by
  have hP := contDiffAt_Psi hz.1 hz.2 hx
  have hmat : ∀ k l : Fin 3, ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) =>
      (((matOfFun p.1.1 * planePinv p.1.2) k l : ℝ) : ℂ)) (z, x) := by
    intro k l
    simp only [Matrix.mul_apply, Fin.sum_univ_three, matOfFun_apply]
    have e1 : ∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => p.1.1 a b) (z, x) :=
      fun a b => (((contDiff_apply ℝ ℝ b).comp (contDiff_apply ℝ (Fin 3 → ℝ) a)).comp
        (contDiff_fst.fst)).contDiffAt
    have e2 : ∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) =>
        planePinv p.1.2 a b) (z, x) := fun a b =>
      ((contDiffAt_planePinv_entry hz.2 a b).of_le (by exact_mod_cast le_top)).comp (z, x)
        (contDiffAt_snd.comp (z, x) contDiffAt_fst)
    have : ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) =>
        p.1.1 k 0 * planePinv p.1.2 0 l + p.1.1 k 1 * planePinv p.1.2 1 l +
          p.1.1 k 2 * planePinv p.1.2 2 l) (z, x) :=
      (((e1 k 0).mul (e2 0 l)).add ((e1 k 1).mul (e2 1 l))).add ((e1 k 2).mul (e2 2 l))
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp (z, x) this
  rw [contDiffAt_pi]
  intro l
  simp only [uRow]
  refine ContDiffAt.sum fun k _ => ?_
  exact ((contDiff_seedRow_apply k).contDiffAt.comp (z, x) hP).mul (hmat k l)

theorem contDiffAt_uPoly (n : ℕ) (m : Fin 3 →₀ ℕ) {z : Par} (hz : GoodPar z)
    {x : Fin 5 → ℝ} (hx : x ∈ Omega) :
    ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => uPoly n m p.1 p.2) (z, x) :=
  (contDiff_polyCoeff n m).contDiffAt.comp (z, x) (contDiffAt_uRow hz hx)

theorem contDiffAt_uTheta (i j : Fin 5) {z : Par} (hz : GoodPar z) {x : Fin 5 → ℝ}
    (hx : x ∈ Omega) :
    ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => uTheta i j p.1 p.2) (z, x) := by
  have hP := contDiffAt_Psi hz.1 hz.2 hx
  have hD := contDiffAt_fderivPsi hz hx
  have hDapp : ∀ (v : Fin 5 → ℝ) (a : Fin 5), ContDiffAt ℝ ∞
      (fun p : Par × (Fin 5 → ℝ) => fderiv ℝ (Psi p.1) p.2 v a) (z, x) := by
    intro v a
    have : ContDiff ℝ ∞ (fun L : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ) => L v a) :=
      ((contDiff_apply ℝ ℝ a).comp
        (ContinuousLinearMap.apply ℝ (Fin 5 → ℝ) v).contDiff)
    exact this.contDiffAt.comp (z, x) hD
  unfold uTheta theta
  refine ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => ?_
  refine (Complex.ofRealCLM.contDiff.contDiffAt.comp (z, x)
    ((hDapp _ a).mul (hDapp _ b))).mul ?_
  have hβ : ∀ c, ContDiffAt ℝ ∞ (fun p : Par × (Fin 5 → ℝ) => seedBeta (Psi p.1 p.2) c) (z, x) :=
    fun c => (contDiff_seedBeta_apply c).contDiffAt.comp (z, x) hP
  exact (((hβ a).mul contDiffAt_const).sub ((hβ b).mul contDiffAt_const))

end TernaryPeriodPolynomials.Argument.ConvergenceC4
