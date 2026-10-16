module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.AdelicSection

@[expose] public section


/-!
# The adelic induced section of the conjugate (antiholomorphic) seed

Formalized by Claude Sonnet 5.5.

`adelicSectionB b` is `cxP b` (coefficientwise complex conjugation) of `adelicSection`; the seed of type `b` is
`summandK b = cxP b ∘ summandPoly` (`ConvergenceC4.summandK_eq`).  The section is again supported on `P₁(ℚ) K(N)`,
left `P₁(ℚ)`-invariant, right `K(N)`-invariant, and on `g_f = π κ` equal to the section of the seed of type `b` at `π_∞⁻¹ g_∞`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N]

/-- **The adelic induced section of the seed of type `b`.** -/
def adelicSectionB (b : Bool) (n : ℕ) (h : ℂ → ℂ) (gR : Matrix (Fin 3) (Fin 3) ℝ) (gf : FiniteGL)
    (y : Fin 5 → ℝ) (i j : Fin 5) : MvPolynomial (Fin 3) ℂ :=
  cxP b (adelicSection N n h gR gf y i j)

theorem adelicSectionB_false (n : ℕ) (h : ℂ → ℂ) (gR : Matrix (Fin 3) (Fin 3) ℝ) (gf : FiniteGL)
    (y : Fin 5 → ℝ) (i j : Fin 5) : adelicSectionB N false n h gR gf y i j = adelicSection N n h gR gf y i j :=
  cxP_false _

/-- **Independence of the decomposition, and the formula: the section of the seed of type `b` at `π_∞⁻¹ g_∞`.** -/
theorem adelicSectionB_of_decomp (hN : 3 ≤ N) (b : Bool) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    {gR : Matrix (Fin 3) (Fin 3) ℝ} (hg : gR.det = 1) {gf : FiniteGL} {π : GL3 ℚ}
    {κ : GL3 IntegralAdeles} (hd : IsDecomp N gf π κ) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) :
    adelicSectionB N b n (hfun f) gR gf y i j = summandK b n (hfun f) (ratReal π⁻¹ * gR) y i j := by
  rw [adelicSectionB, adelicSection_of_decomp N hN n f hg hd hy i j, summandK_eq]

theorem adelicSectionB_mul_ker (hN : 3 ≤ N) (b : Bool) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    {gR : Matrix (Fin 3) (Fin 3) ℝ} (hg : gR.det = 1) (gf : FiniteGL) {κ' : GL3 IntegralAdeles}
    (hk : κ' ∈ levelKernel N 3) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) :
    adelicSectionB N b n (hfun f) gR (gf * GeneralLinearGroup.map integralEmbedding κ') y i j =
      adelicSectionB N b n (hfun f) gR gf y i j := by
  unfold adelicSectionB
  rw [adelicSection_mul_ker N hN n f hg gf hk hy i j]

theorem adelicSectionB_planeDet_mul (hN : 3 ≤ N) (b : Bool) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    {gR : Matrix (Fin 3) (Fin 3) ℝ} (hg : gR.det = 1) (gf : FiniteGL) {p : GL3 ℚ} (hp : PlaneDet p)
    {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) :
    adelicSectionB N b n (hfun f) (ratReal p * gR) (rationalFinite p * gf) y i j =
      adelicSectionB N b n (hfun f) gR gf y i j := by
  unfold adelicSectionB
  rw [adelicSection_planeDet_mul N hN n f hg gf hp hy i j]

end TernaryPeriodPolynomials.Argument.FormClassK
