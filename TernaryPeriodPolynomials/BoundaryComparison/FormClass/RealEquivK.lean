module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.TFormK

@[expose] public section


/-!
# The real component of `g`: right equivariance of the intertwiner

Formalized by Claude Sonnet 5.5.
Paper: `ar:eq:seed-transform`.

`adelicOfPair gR gf = (gR, gf) ∈ GL₃(ℝ × 𝔸_f)` for `gR ∈ SL₃(ℝ)`.
* `adelicSection_mul_real`: the section is right-equivariant for the real group: `φ(g_∞ g_R, g_f) = ρ(g_R)⁻¹ g_R^* [φ(g_∞, g_f)]`.
* `TcoefG_eq`: for `g = (g_R, ι(k⁻¹))` and every `y ∈ Ω`, the coefficients of `(Tφ^b)(g)(y)` are those of
  `ρ(g_R)⁻¹ g_R^* TformK` at `y` (the pullback by the plane action `planeAct g_R`, `g_R · basePt`).  For `y = basePt` this is the
  value of `Tφ^b(g)` at the base frame, with `g_∞ · basePt = planeAct g_R basePt`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open MvPolynomial
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.EisensteinDual TernaryPeriodPolynomials.Argument.GammaNFaces

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

theorem sl_inv_row (gR : Matrix.SpecialLinearGroup (Fin 3) ℝ) (i j : Fin 3) :
    ∑ l, (gR : Matrix (Fin 3) (Fin 3) ℝ) i l * ((gR⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) l j =
      if i = j then 1 else 0 := by
  have h := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 3) ℝ => (M : Matrix (Fin 3) (Fin 3) ℝ) i j) (mul_inv_cancel gR)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_apply, Matrix.one_apply] at h
  exact h

theorem sl_inv_col (gR : Matrix.SpecialLinearGroup (Fin 3) ℝ) (i j : Fin 3) :
    ∑ l, ((gR⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) i l * (gR : Matrix (Fin 3) (Fin 3) ℝ) l j =
      if i = j then 1 else 0 := by
  have h := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 3) ℝ => (M : Matrix (Fin 3) (Fin 3) ℝ) i j) (inv_mul_cancel gR)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_apply, Matrix.one_apply] at h
  exact h

/-- The element `(gR, gf)` of `GL₃(𝔸) = GL₃(ℝ × 𝔸_f)`, `gR ∈ SL₃(ℝ)`. -/
def adelicOfPair (gR : Matrix.SpecialLinearGroup (Fin 3) ℝ) (gf : FiniteGL) : AdelicGL where
  val := Matrix.of fun i j => ((gR : Matrix (Fin 3) (Fin 3) ℝ) i j, gf.val i j)
  inv := Matrix.of fun i j => (((gR⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) i j, gf.inv i j)
  val_inv := by
    refine Matrix.ext fun i j => Prod.ext ?_ ?_
    · have := sl_inv_row gR i j
      by_cases h : i = j <;> simpa [Matrix.mul_apply, Matrix.one_apply, Prod.fst_sum, h] using this
    · have := congrArg (fun M : Matrix (Fin 3) (Fin 3) FiniteAdeles => M i j) gf.val_inv
      by_cases h : i = j <;> simpa [Matrix.mul_apply, Matrix.one_apply, Prod.snd_sum, h] using this
  inv_val := by
    refine Matrix.ext fun i j => Prod.ext ?_ ?_
    · have := sl_inv_col gR i j
      by_cases h : i = j <;> simpa [Matrix.mul_apply, Matrix.one_apply, Prod.fst_sum, h] using this
    · have := congrArg (fun M : Matrix (Fin 3) (Fin 3) FiniteAdeles => M i j) gf.inv_val
      by_cases h : i = j <;> simpa [Matrix.mul_apply, Matrix.one_apply, Prod.snd_sum, h] using this

theorem realGroup_adelicOfPair (gR : Matrix.SpecialLinearGroup (Fin 3) ℝ) (gf : FiniteGL) :
    ((realGroup (adelicOfPair gR gf) : GL3 ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = (gR : Matrix (Fin 3) (Fin 3) ℝ) := by
  refine Matrix.ext fun i j => ?_
  simp [realGroup, adelicOfPair, GeneralLinearGroup.map_apply]

theorem finiteGroup_adelicOfPair (gR : Matrix.SpecialLinearGroup (Fin 3) ℝ) (gf : FiniteGL) :
    finiteGroup (adelicOfPair gR gf) = gf := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  simp [finiteGroup, adelicOfPair, GeneralLinearGroup.map_apply]

theorem realMatOf_unip_pair (gR : Matrix.SpecialLinearGroup (Fin 3) ℝ) (gf : FiniteGL) (u : Adeles × Adeles) :
    realMatOf (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOfPair gR gf) =
      gReal ![u.1.1, u.2.1] * (gR : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h1 := realMatOf_unip u
  unfold realMatOf at h1 ⊢
  rw [mul_one] at h1
  rw [map_mul, Units.val_mul, realGroup_adelicOfPair, h1]

theorem finiteGroup_unip_pair (gR : Matrix.SpecialLinearGroup (Fin 3) ℝ) (gf : FiniteGL) (u : Adeles × Adeles) :
    finiteGroup (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOfPair gR gf) = gFin (u.1.2, u.2.2) * gf := by
  have := finiteGroup_unip u
  rw [mul_one] at this
  rw [map_mul, finiteGroup_adelicOfPair, this]

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- **Right equivariance of the section for the real group.** -/
theorem adelicSection_mul_real (hN : 3 ≤ N) {gA gR : Matrix (Fin 3) (Fin 3) ℝ} (hA : gA.det = 1) (hR : gR.det = 1)
    (gf : FiniteGL) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) :
    adelicSection N n (hfun f) (gA * gR) gf y i j =
      rho gR⁻¹ (formPullback (planeAct gR) (fun y' a b => adelicSection N n (hfun f) gA gf y' a b) y i j) := by
  by_cases hd : ∃ π κ, IsDecomp N gf π κ
  · obtain ⟨π, κ, hd⟩ := hd
    have hy' := planeAct_mem hR hy
    have hg : (ratReal π⁻¹ * gA).det = 1 := by rw [Matrix.det_mul, ratReal_inv_det hd.ppos, hA, one_mul]
    rw [adelicSection_of_decomp N hN n f (by rw [Matrix.det_mul, hA, hR, one_mul]) hd hy i j]
    have hin : ∀ a b, adelicSection N n (hfun f) gA gf (planeAct gR y) a b =
        summandPoly n (hfun f) (ratReal π⁻¹ * gA) (planeAct gR y) a b := fun a b =>
      adelicSection_of_decomp N hN n f hA hd hy' a b
    unfold formPullback
    simp only [hin]
    rw [← Matrix.mul_assoc]
    have := summandPoly_mul_eq n (hfun f) hg hR hy i j
    unfold formPullback at this
    exact this
  · have h0 : ∀ g : Matrix (Fin 3) (Fin 3) ℝ, ∀ y' a b, adelicSection N n (hfun f) g gf y' a b = 0 :=
      fun g y' a b => adelicSection_of_not N n _ g hd y' a b
    rw [h0]
    unfold formPullback
    simp [h0, rho]

end TernaryPeriodPolynomials.Argument.FormClassK
