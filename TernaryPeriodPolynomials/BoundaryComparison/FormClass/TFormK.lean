module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.PsiFinal

@[expose] public section


/-!
# The `E`-valued intertwiner as a polynomial-valued form, and its commutation with the line-face pullback

Formalized by Claude Sonnet 5.5.

`TcoefK b k y i j m = ∫_{𝔸²} (φ^b(w₀⁻¹u(s,t) g)(y; i, j)).coeff m ds dt` for `g = (1, ι(k⁻¹))`, and `TformK` the polynomial with these
coefficients.  For `y ∈ Ω` each coefficient is absolutely convergent (`TcoefK_integrable`), and
`fPull_TformK`: the face pullback of `TformK` is the integral of the face pullback of the integrand (`T` commutes with `jFace^*`).
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

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- **The coefficients of `(Tφ^b)(g)(y; i, j)`** at `g = (1, ι(k⁻¹))`, literally as integrals over `𝔸²`. -/
def TcoefK (b : Bool) (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) : ℂ :=
  ∫ u : Adeles × Adeles, (cxP b (adelicSectionG N n (hfun f)
    (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOf (kInvFin k)) y i j)).coeff m ∂radicalMeasure

theorem integrand_eq_FzE (b : Bool) (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (u : Adeles × Adeles) :
    (cxP b (adelicSectionG N n (hfun f) (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOf (kInvFin k)) y i j)).coeff m =
      FzE N k n f b y i j m (radicalEquiv u) := by
  unfold adelicSectionG FzE
  rw [realMatOf_unip_adelicOf, finiteGroup_unip_adelicOf]
  rfl

theorem TcoefK_integrable (hN : 3 ≤ N) (hn : 4 ≤ n) (b : Bool) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) :
    Integrable (fun u : Adeles × Adeles => (cxP b (adelicSectionG N n (hfun f)
      (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOf (kInvFin k)) y i j)).coeff m) radicalMeasure := by
  simp_rw [integrand_eq_FzE N k n f b y i j m]
  exact (radical_integrable_iff (FzE N k n f b y i j m)).2 (FzE_integral N k n f hN hn b hy i j m).1

/-- **`Tφ^b(g)(y; i, j)` has the orbit-sum value** (absolutely convergent, any `y ∈ Ω`). -/
theorem TcoefK_value (hN : 3 ≤ N) (hn : 4 ≤ n) (b : Bool) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) :
    TcoefK N k n f b y i j m = cx b (∑' o : FreeOrbK N k, ∫ v : Fin 2 → ℝ, psiO N k n f y i j m o ((N : ℝ) • v)) := by
  unfold TcoefK
  simp_rw [integrand_eq_FzE N k n f b y i j m]
  rw [radical_integral_eq (FzE N k n f b y i j m)]
  exact (FzE_integral N k n f hN hn b hy i j m).2

theorem adelicSection_isHomogeneous (gR : Matrix (Fin 3) (Fin 3) ℝ) (hg : gR.det = 1) (gf : FiniteGL) (y : Fin 5 → ℝ)
    (i j : Fin 5) : (adelicSection N n (hfun f) gR gf y i j).IsHomogeneous n := by
  unfold adelicSection
  split_ifs with hd
  · have hπ := hd.choose_spec.choose_spec.ppos
    refine summandPoly_isHomogeneous n (hfun f) ?_ y i j
    rw [Matrix.det_mul, ratReal_inv_det hπ, hg, one_mul]
  · exact MvPolynomial.isHomogeneous_zero _ _ _

theorem TcoefK_eq_zero_of_not_mem (b : Bool) (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (hm : m ∉ monSet n) :
    TcoefK N k n f b y i j m = 0 := by
  unfold TcoefK
  have : ∀ u : Adeles × Adeles, (cxP b (adelicSectionG N n (hfun f)
      (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOf (kInvFin k)) y i j)).coeff m = 0 := by
    intro u
    by_contra hne
    have hh := isHomogeneous_cxP b (adelicSection_isHomogeneous N n f (realMatOf (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOf (kInvFin k)))
      (by rw [realMatOf_unip_adelicOf]; exact gReal_det _) (finiteGroup (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOf (kInvFin k))) y i j)
    exact hm (mem_monSet_of_coeff_ne hh hne)
  simp [this]

/-- **The polynomial `Tφ^b(g)(y; i, j)`.** -/
def TformK (b : Bool) (y : Fin 5 → ℝ) (i j : Fin 5) : MvPolynomial (Fin 3) ℂ :=
  ∑ m ∈ monSet n, monomial m (TcoefK N k n f b y i j m)

theorem coeff_TformK (b : Bool) (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    (TformK N k n f b y i j).coeff m = TcoefK N k n f b y i j m := by
  unfold TformK
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ monSet n
  · rw [Finset.sum_eq_single m]
    · simp
    · intro m' _ hne; simp [hne]
    · intro h; exact absurd hm h
  · rw [TcoefK_eq_zero_of_not_mem N k n f b y i j m hm]
    exact Finset.sum_eq_zero fun m' hm' => by
      have : m' ≠ m := fun h => hm (h ▸ hm')
      simp [this]

/-- **`T` commutes with the line-face pullback**: the `(x; e_p, e_q)`, `m` coordinate of `jFace^*(Tφ^b)` is the integral over `𝔸²` of the
same coordinate of `jFace^*(φ^b(w₀⁻¹u g))`. -/
theorem fPull_TformK (hN : 3 ≤ N) (hn : 4 ≤ n) (b : Bool) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    (fPull jFace (fun y i j => TformK N k n f b y i j) x p q).coeff m =
      ∫ u, printedIntegrandB N n f b x p q m (adelicOf (kInvFin k)) u ∂radicalMeasure := by
  have hy : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  unfold printedIntegrandB fPull
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, coeff_TformK]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun c _ =>
    (TcoefK_integrable N k n f hN hn b hy a c m).const_mul _))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun c _ => (TcoefK_integrable N k n f hN hn b hy a c m).const_mul _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_const_mul]
  rfl

end TernaryPeriodPolynomials.Argument.FormClassK
