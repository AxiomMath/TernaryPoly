module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Conj
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Cusp.Coset

@[expose] public section


/-!
# Proposition C.4 at a plane cusp: the series for either type of seed

The series `∑_{γ ∈ Γ_P\Γ} ρ(aγ)⁻¹ (aγ)^* ω` over the cosets of the stabilizer of the cusp `D`
(`CuspData`), for the holomorphic (`b = false`) or antiholomorphic (`b = true`) seed `ω` of a cusp
form `f`: normal convergence of every derivative on compact subsets of `Ω`
(`exists_summable_jet_bound_K`, from the jet bound of a single term, which holds for every real
matrix of determinant one), smoothness and termwise differentiation (`seriesCoeffK_smooth`),
closedness (`seriesCoeffK_closedAt`), and the polynomial-valued form `seriesFormK`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

section CuspSeries

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable (b : Bool) (D : CuspData) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]
  (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

theorem det_cusp_mul (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) : (D.a * realMat γ).det = 1 := by
  rw [Matrix.det_mul, D.det_a, det_realMat, one_mul]

/-- The term of the series at the cusp `D`, for the seed of type `b`, attached to a coset (through
a chosen representative): the `m`-th coefficient of the `(i, j)` component of
`ρ(aγ)⁻¹ (aγ)^* ω`. -/
def termFunK (c : CuspCoset Γ D.r) (i j : Fin 5) (m : Fin 3 →₀ ℕ) : (Fin 5 → ℝ) → ℂ :=
  fun x => (summandK b n (hfun f) (D.a * realMat (Quotient.out c).1) x i j).coeff m

/-- The coefficients of the series at the cusp `D`. -/
def seriesCoeffK (i j : Fin 5) (m : Fin 3 →₀ ℕ) (x : Fin 5 → ℝ) : ℂ :=
  ∑' c : CuspCoset Γ D.r, termFunK b D Γ n f c i j m x

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem termFunK_eq (c : CuspCoset Γ D.r) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    termFunK b D Γ n f c i j m = fun x => cxL b
      ((summandPoly n (hfun f) (D.a * realMat (Quotient.out c).1) x i j).coeff m) := by
  funext x
  rw [cxL_apply]
  unfold termFunK
  rw [summandK_eq, coeff_cxP]

include Λ

omit [Λ.HasDetOne] [Λ.IsArithmetic] in
theorem contDiffOn_termFunK (c : CuspCoset Γ D.r) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ ∞ (termFunK b D Γ n f c i j m) Omega := by
  rw [termFunK_eq]
  exact (cxL b).contDiff.comp_contDiffOn
    (contDiffOn_term n (hfun f) (hfun_differentiableOn Λ n f) (det_cusp_mul D _) i j m)

omit [Λ.HasDetOne] in
/-- **Normal convergence of every derivative at the cusp `D`.** -/
theorem exists_summable_jet_bound_K (hn : 4 ≤ n) {K : Set (Fin 5 → ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ Omega) (N : ℕ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ∃ B : CuspCoset Γ D.r → ℝ, Summable B ∧ ∀ (c : CuspCoset Γ D.r), ∀ x ∈ K,
      ‖iteratedFDeriv ℝ N (termFunK b D Γ n f c i j m) x‖ ≤ B c := by
  obtain ⟨Ch, hCh⟩ := hfun_bound Λ n f
  obtain ⟨C, hC⟩ := term_jet_bound n (hfun f) Ch hCh (hfun_differentiableOn Λ n f) hK hKΩ N i j m
  obtain ⟨B, hBs, hB⟩ := exists_summable_dominating_cusp D Γ n hn hK hKΩ
    (fun γ q => ‖iteratedFDeriv ℝ N (fun x =>
      (summandPoly n (hfun f) (D.a * realMat γ.1) x i j).coeff m) q‖) C
    (fun γ q hq => hC _ (det_cusp_mul D γ.1) q hq)
  refine ⟨B, hBs, fun c x hx => ?_⟩
  have := hB (Quotient.out c) x hx
  rw [Quotient.out_eq] at this
  rw [termFunK_eq]
  exact ((cxL b).norm_iteratedFDeriv_comp_left _ x N).le.trans this

omit [Λ.HasDetOne] in
/-- The series of coefficients is `C^∞` on `Ω` and may be differentiated termwise. -/
theorem seriesCoeffK_smooth (hn : 4 ≤ n) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ ∞ (seriesCoeffK b D Γ n f i j m) Omega ∧
      ∀ (k : ℕ), ∀ x ∈ Omega, iteratedFDeriv ℝ k (seriesCoeffK b D Γ n f i j m) x =
        ∑' c : CuspCoset Γ D.r, iteratedFDeriv ℝ k (termFunK b D Γ n f c i j m) x :=
  contDiffOn_tsum_local isOpen_Omega (fun c => termFunK b D Γ n f c i j m)
    (fun c => contDiffOn_termFunK b D Γ Λ n f c i j m)
    (fun _K hK hKΩ k => exists_summable_jet_bound_K b D Γ Λ n f hn hK hKΩ k i j m)

omit [Λ.HasDetOne] in
theorem summable_termFunK_val (hn : 4 ≤ n) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a c : Fin 5)
    (m : Fin 3 →₀ ℕ) : Summable (fun x : CuspCoset Γ D.r => termFunK b D Γ n f x a c m y) := by
  obtain ⟨B, hB, hBd⟩ := exists_summable_jet_bound_K b D Γ Λ n f hn (isCompact_singleton (x := y))
    (Set.singleton_subset_iff.2 hy) 0 a c m
  refine Summable.of_norm_bounded hB fun x => ?_
  have := hBd x y rfl
  simpa using this

omit Λ in
theorem fderiv_cxL_comp (g : (Fin 5 → ℝ) → ℂ) (x v : Fin 5 → ℝ) :
    fderiv ℝ (fun y => cxL b (g y)) x v = cxL b (fderiv ℝ g x v) := by
  have := (cxL b).toContinuousLinearEquiv.comp_fderiv (f := g) (x := x)
  have h2 := congrArg (fun L => L v) this
  exact h2

omit [Λ.HasDetOne] [Λ.IsArithmetic] in
theorem closedAt_termFunK {x : Fin 5 → ℝ} (hx : x ∈ Omega) (c : CuspCoset Γ D.r)
    (m : Fin 3 →₀ ℕ) : ClosedAt (fun a b' y => termFunK b D Γ n f c a b' m y) x := by
  intro i j k
  have h := closedAt_summand_coeff n (hfun f) (hfun_differentiableOn Λ n f)
    (det_cusp_mul D (Quotient.out c).1) hx m i j k
  beta_reduce at h ⊢
  rw [termFunK_eq b D Γ n f c j k m, termFunK_eq b D Γ n f c i k m, termFunK_eq b D Γ n f c i j m,
    fderiv_cxL_comp, fderiv_cxL_comp, fderiv_cxL_comp, ← map_sub, ← map_add, h, map_zero]

omit [Λ.HasDetOne] in
theorem summable_fderiv_termFunK (hn : 4 ≤ n) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) (v : Fin 5 → ℝ) :
    Summable (fun c : CuspCoset Γ D.r => fderiv ℝ (termFunK b D Γ n f c i j m) x v) := by
  obtain ⟨B, hB, hBd⟩ := exists_summable_jet_bound_K b D Γ Λ n f hn (isCompact_singleton (x := x))
    (Set.singleton_subset_iff.2 hx) 1 i j m
  refine Summable.of_norm_bounded (hB.mul_left ‖v‖) fun c => ?_
  have h1 := hBd c x rfl
  rw [norm_iteratedFDeriv_one] at h1
  calc ‖fderiv ℝ (termFunK b D Γ n f c i j m) x v‖
      ≤ ‖fderiv ℝ (termFunK b D Γ n f c i j m) x‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ B c * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖v‖ * B c := by ring

omit [Λ.HasDetOne] in
theorem seriesCoeffK_fderiv_apply (hn : 4 ≤ n) (i j : Fin 5) (m : Fin 3 →₀ ℕ) {x : Fin 5 → ℝ}
    (hx : x ∈ Omega) (v : Fin 5 → ℝ) :
    fderiv ℝ (seriesCoeffK b D Γ n f i j m) x v =
      ∑' c : CuspCoset Γ D.r, fderiv ℝ (termFunK b D Γ n f c i j m) x v := by
  have h := (seriesCoeffK_smooth b D Γ Λ n f hn i j m).2 1 x hx
  obtain ⟨B, hB, hBd⟩ := exists_summable_jet_bound_K b D Γ Λ n f hn (isCompact_singleton (x := x))
    (Set.singleton_subset_iff.2 hx) 1 i j m
  have hsum : Summable (fun c : CuspCoset Γ D.r =>
      iteratedFDeriv ℝ 1 (termFunK b D Γ n f c i j m) x) :=
    Summable.of_norm_bounded hB fun c => hBd c x rfl
  have := congrArg (fun L => L (fun _ => v)) h
  simp only [iteratedFDeriv_one_apply] at this
  rw [this]
  have hev := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Fin 5 → ℝ) ℂ
    (fun _ => v)).map_tsum hsum
  simpa using hev

omit [Λ.HasDetOne] in
theorem seriesCoeffK_closedAt (hn : 4 ≤ n) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (m : Fin 3 →₀ ℕ) :
    ClosedAt (fun a b' y => seriesCoeffK b D Γ n f a b' m y) x := by
  intro i j k
  rw [seriesCoeffK_fderiv_apply b D Γ Λ n f hn j k m hx,
    seriesCoeffK_fderiv_apply b D Γ Λ n f hn i k m hx,
    seriesCoeffK_fderiv_apply b D Γ Λ n f hn i j m hx]
  rw [← Summable.tsum_sub (summable_fderiv_termFunK b D Γ Λ n f hn hx j k m _)
      (summable_fderiv_termFunK b D Γ Λ n f hn hx i k m _),
    ← Summable.tsum_add ((summable_fderiv_termFunK b D Γ Λ n f hn hx j k m _).sub
      (summable_fderiv_termFunK b D Γ Λ n f hn hx i k m _))
      (summable_fderiv_termFunK b D Γ Λ n f hn hx i j m _)]
  exact (tsum_congr fun c => closedAt_termFunK b D Γ Λ n f hx c m i j k).trans tsum_zero

end CuspSeries

/-! ### The series as a polynomial-valued form -/

section CuspForm

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable (b : Bool) (D : CuspData) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]
  (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem termFunK_coeff_eq_zero (c : CuspCoset Γ D.r) (y : Fin 5 → ℝ) (i j : Fin 5)
    {m : Fin 3 →₀ ℕ} (hm : m ∉ monSet n) : termFunK b D Γ n f c i j m y = 0 := by
  have h0 : (summandPoly n (hfun f) (D.a * realMat (Quotient.out c).1) y i j).coeff m = 0 := by
    by_contra hne
    exact hm (mem_monSet_of_coeff_ne
      (summandPoly_isHomogeneous n (hfun f) (det_cusp_mul D _) y i j) hne)
  rw [termFunK_eq]
  beta_reduce
  rw [h0]
  exact map_zero _

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem seriesCoeffK_eq_zero (y : Fin 5 → ℝ) (i j : Fin 5) {m : Fin 3 →₀ ℕ}
    (hm : m ∉ monSet n) : seriesCoeffK b D Γ n f i j m y = 0 := by
  unfold seriesCoeffK
  simp [termFunK_coeff_eq_zero b D Γ n f _ y i j hm]

/-- **The global two-form `𝓔` at the cusp `D`** (`ar:eq:Eseries`) with polynomial coefficients: its
`(a, b)` component at `y` is the homogeneous polynomial of degree `n` whose coefficients are those
of the series. -/
def seriesFormK (y : Fin 5 → ℝ) (i j : Fin 5) : MvPolynomial (Fin 3) ℂ :=
  ∑ m ∈ monSet n, monomial m (seriesCoeffK b D Γ n f i j m y)

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem coeff_seriesFormK (m : Fin 3 →₀ ℕ) (y : Fin 5 → ℝ) (i j : Fin 5) :
    (seriesFormK b D Γ n f y i j).coeff m = seriesCoeffK b D Γ n f i j m y := by
  unfold seriesFormK
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ monSet n
  · rw [Finset.sum_eq_single m (fun m' _ hne => by simp [hne]) (fun h => absurd hm h)]
    simp
  · rw [Finset.sum_eq_zero fun m' hm' => by
      have : m' ≠ m := fun h => hm (h ▸ hm')
      simp [this]]
    exact (seriesCoeffK_eq_zero b D Γ n f y i j hm).symm

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem seriesFormK_isHomogeneous (y : Fin 5 → ℝ) (i j : Fin 5) :
    MvPolynomial.IsHomogeneous (seriesFormK b D Γ n f y i j) n := by
  intro d hd
  by_cases hdm : d ∈ monSet n
  · exact weight_eq_of_mem_monSet hdm
  · exfalso; apply hd; rw [coeff_seriesFormK]; exact seriesCoeffK_eq_zero b D Γ n f y i j hdm

end CuspForm

end TernaryPeriodPolynomials.Argument.ConvergenceC4
