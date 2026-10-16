module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.RealEquivK

@[expose] public section


/-!
# The real component of `g`: `Tφ^b(g_R, ι(k⁻¹))` is the real translate of `Tφ^b(1, ι(k⁻¹))`

Formalized by Claude Sonnet 5.5.

`TcoefG b gR y i j m`: the `m`-th coefficient of `(Tφ^b)(g)(y; i, j)`, `g = (g_R, ι(k⁻¹))`, `g_R ∈ SL₃(ℝ)`, as the literal integral over `𝔸²`.
`TcoefG_eq`: it is the `m`-th coefficient of `ρ(g_R)⁻¹ (g_R)^* TformK` at `y`, i.e. `Tφ^b(g_R, ι(k⁻¹)) = ρ(g_R)⁻¹ g_R^*[Tφ^b(1, ι(k⁻¹))]`
(the induced-representation transformation law for the real group).  At the base point `y = basePt` this is the value of `Tφ^b(g)` in the
base frame at `g_R · basePt = planeAct g_R basePt`.
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

/-- **The coefficients of `(Tφ^b)(g_R, ι(k⁻¹))(y; i, j)`**, literally as integrals over `𝔸²`. -/
def TcoefG (b : Bool) (gR : Matrix.SpecialLinearGroup (Fin 3) ℝ) (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) : ℂ :=
  ∫ u : Adeles × Adeles, (cxP b (adelicSectionG N n (hfun f)
    (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOfPair gR (kInvFin k)) y i j)).coeff m ∂radicalMeasure

omit [NeZero N] in
theorem coeff_rho_formPullback (W : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (hW : ∀ y' a c, (W y' a c).IsHomogeneous n) (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)) (p : Fin 5 → ℝ) (i j : Fin 5)
    (G : Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 →₀ ℕ) :
    (rho G (formPullback Φ W p i j)).coeff m = ∑ m' ∈ monSet n, ∑ a : Fin 5, ∑ c : Fin 5,
      ((((fderiv ℝ Φ p (Pi.single i 1) a * fderiv ℝ Φ p (Pi.single j 1) c : ℝ)) : ℂ) * (W (Φ p) a c).coeff m') *
        (rho G (monomial m' 1)).coeff m := by
  have hhom : (formPullback Φ W p i j).IsHomogeneous n := by
    unfold formPullback
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ => ?_
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun c _ => ?_
    exact (hW _ a c).C_mul _
  rw [coeff_rho_expansion hhom G m]
  refine Finset.sum_congr rfl fun m' _ => ?_
  unfold formPullback
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, Finset.sum_mul]

theorem integrand_eq_pair (hN : 3 ≤ N) (b : Bool) (gR : Matrix.SpecialLinearGroup (Fin 3) ℝ) {y : Fin 5 → ℝ}
    (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) (u : Adeles × Adeles) :
    (cxP b (adelicSectionG N n (hfun f) (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOfPair gR (kInvFin k)) y i j)).coeff m =
      (rho (gR : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ (formPullback (planeAct (gR : Matrix (Fin 3) (Fin 3) ℝ))
        (fun y' a c => cxP b (adelicSectionG N n (hfun f) (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOf (kInvFin k)) y' a c))
        y i j)).coeff m := by
  have h := adelicSection_mul_real N n f hN (gA := gReal ![u.1.1, u.2.1]) (gR := (gR : Matrix (Fin 3) (Fin 3) ℝ))
    (gReal_det _) gR.2 (gFin (u.1.2, u.2.2) * kInvFin k) hy i j
  unfold adelicSectionG
  simp only [realMatOf_unip_pair, finiteGroup_unip_pair, realMatOf_unip_adelicOf, finiteGroup_unip_adelicOf]
  rw [h, formPullback_cxP b (planeAct (gR : Matrix (Fin 3) (Fin 3) ℝ)) (fun y' a c => adelicSection N n (hfun f) (gReal ![u.1.1, u.2.1]) (gFin (u.1.2, u.2.2) * kInvFin k) y' a c), rho_cxP]

theorem TformK_isHomogeneous (b : Bool) (y : Fin 5 → ℝ) (i j : Fin 5) :
    (TformK N k n f b y i j).IsHomogeneous n := by
  unfold TformK
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun m hm => ?_
  exact MvPolynomial.isHomogeneous_monomial _ (by
    have := weight_eq_of_mem_monSet hm
    rw [Finsupp.degree_eq_sum]
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this)

/-- **The real component of `g`.** For `g = (g_R, ι(k⁻¹))`, `g_R ∈ SL₃(ℝ)`, and every `y ∈ Ω`, the (absolutely convergent) integral
`∫_{𝔸²} φ^b(w₀⁻¹u(s,t)g)(y; i, j)` has the coefficients of `ρ(g_R)⁻¹ g_R^* TformK` at `y`:
`Tφ^b(g_R, ι(k⁻¹)) = ρ(g_R)⁻¹ g_R^*[Tφ^b(1, ι(k⁻¹))]`. -/
theorem TcoefG_eq (hN : 3 ≤ N) (hn : 4 ≤ n) (b : Bool) (gR : Matrix.SpecialLinearGroup (Fin 3) ℝ) {y : Fin 5 → ℝ}
    (hy : y ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    TcoefG N k n f b gR y i j m =
      (rho (gR : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ (formPullback (planeAct (gR : Matrix (Fin 3) (Fin 3) ℝ))
        (fun y' a c => TformK N k n f b y' a c) y i j)).coeff m := by
  have hy' : planeAct (gR : Matrix (Fin 3) (Fin 3) ℝ) y ∈ Omega := planeAct_mem gR.2 hy
  have hW : ∀ u : Adeles × Adeles, ∀ y' a c, (cxP b (adelicSectionG N n (hfun f)
      (weyl⁻¹ * lineUnipotent u.1 u.2 * adelicOf (kInvFin k)) y' a c)).IsHomogeneous n := by
    intro u y' a c
    unfold adelicSectionG
    exact isHomogeneous_cxP b (adelicSection_isHomogeneous N n f _
      (by rw [realMatOf_unip_adelicOf]; exact gReal_det _) _ y' a c)
  unfold TcoefG
  simp_rw [integrand_eq_pair N k n f hN b gR hy i j m]
  simp_rw [coeff_rho_formPullback n _ (hW _) _ _ i j _ m]
  rw [coeff_rho_formPullback n _ (fun y' a c => TformK_isHomogeneous N k n f b y' a c) _ _ i j _ m]
  rw [integral_finsetSum _ (fun m' _ => integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun c _ =>
    ((TcoefK_integrable N k n f hN hn b hy' a c m').const_mul _).mul_const _)))]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun c _ =>
    ((TcoefK_integrable N k n f hN hn b hy' a c m').const_mul _).mul_const _))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun c _ => ((TcoefK_integrable N k n f hN hn b hy' a c m').const_mul _).mul_const _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_mul_const, integral_const_mul, coeff_TformK]
  rfl

end TernaryPeriodPolynomials.Argument.FormClassK
