module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Series
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Term
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.ClosedTerms

@[expose] public section


/-!
# Proposition C.4: `Γ`-equivariance and the polynomial-valued global form

The series `E_P(ω_h) = ∑_{γ ∈ Γ_P\Γ} ρ(γ)⁻¹ γ^* ω_h` of `ar:prop:convergence`, packaged as a
function `seriesForm` on `Ω` with values in the homogeneous polynomials of degree `n` in three
variables, together with the cocycle relation of its summands (`summandPoly_mul_eq`), the right
action of `Γ` on the cosets (`cosetMulR`), and the equivariance `ρ(δ)⁻¹ δ^* E = E`
(`seriesForm_equivariant`) for every `δ ∈ Γ`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

/-! ### The right action of `Γ` on the cosets, and the cocycle relation of the summands -/

section CosetAction

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))

/-- Right multiplication by `δ ∈ Γ` on `Γ_P \ Γ`. -/
def cosetMulR (δ : Γ) : PlaneCoset Γ → PlaneCoset Γ :=
  Quotient.map (fun a : Γ => a * δ) (by
    intro a b hab
    have h := QuotientGroup.rightRel_apply.1 hab
    refine QuotientGroup.rightRel_apply.2 ?_
    simpa [mul_assoc] using h)

theorem cosetMulR_mk (δ a : Γ) : cosetMulR Γ δ (Quotient.mk _ a) = Quotient.mk _ (a * δ) := rfl

/-- Right multiplication by `δ` is a bijection of `Γ_P \ Γ`. -/
def cosetMulREquiv (δ : Γ) : PlaneCoset Γ ≃ PlaneCoset Γ where
  toFun := cosetMulR Γ δ
  invFun := cosetMulR Γ δ⁻¹
  left_inv c := by
    induction c using Quotient.inductionOn with | _ a => ?_
    simp [cosetMulR_mk]
  right_inv c := by
    induction c using Quotient.inductionOn with | _ a => ?_
    simp [cosetMulR_mk]

end CosetAction

/-- **Cocycle relation.** `S_{γδ}(x) = ρ(δ)⁻¹ δ^* S_γ (x)`. -/
theorem summandPoly_mul_eq (n : ℕ) (h : ℂ → ℂ) {g d : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : g.det = 1) (hd : d.det = 1) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) :
    summandPoly n h (g * d) x i j =
      SeedC3.rho d⁻¹ (formPullback (planeAct d) (fun y a b => summandPoly n h g y a b) x i j) := by
  have hx' := planeAct_mem hd hx
  have hev : planeAct (g * d) =ᶠ[nhds x] planeAct g ∘ planeAct d :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hx) fun z hz => planeAct_mul hd hz
  unfold summandPoly
  rw [formPullback_congr _ hev, formPullback_comp _ _ _ x (differentiableAt_planeAct hd hx)
    (differentiableAt_planeAct hg hx') i j, formPullback_rho, rho_mul, Matrix.mul_inv_rev]

/-! ### The series as a polynomial-valued form -/

theorem weight_eq_of_mem_monSet {n : ℕ} {m : Fin 3 →₀ ℕ} (hm : m ∈ monSet n) :
    Finsupp.weight (1 : Fin 3 → ℕ) m = n := by
  rw [monSet, Finset.mem_finsuppAntidiag] at hm
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using hm.1

theorem summandPoly_isHomogeneous (n : ℕ) (h : ℂ → ℂ) {g : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : g.det = 1) (q : Fin 5 → ℝ) (i j : Fin 5) :
    MvPolynomial.IsHomogeneous (summandPoly n h g q i j) n := by
  rw [summandPoly_eq n h hg q i j]
  have hl : MvPolynomial.IsHomogeneous (∑ l : Fin 3, C (∑ k : Fin 3, seedRow (planeAct g q) k *
      (g k l : ℂ)) * (X l : MvPolynomial (Fin 3) ℂ)) 1 :=
    MvPolynomial.IsHomogeneous.sum _ _ _ fun l _ => isHomogeneous_C_mul_X _ _
  have := (isHomogeneous_C (Fin 3) (scalarPullback (planeAct g) (seedForm0 h) q i j)).mul
    (hl.pow n)
  simpa using this

section SeriesForm

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]
  (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem termFun_coeff_eq_zero (c : PlaneCoset Γ) (y : Fin 5 → ℝ) (a b : Fin 5) {m : Fin 3 →₀ ℕ}
    (hm : m ∉ monSet n) : termFun Γ n f c a b m y = 0 := by
  unfold termFun
  by_contra hne
  exact hm (mem_monSet_of_coeff_ne (summandPoly_isHomogeneous n (hfun f) (det_realMat _) y a b) hne)

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem seriesCoeff_eq_zero (y : Fin 5 → ℝ) (a b : Fin 5) {m : Fin 3 →₀ ℕ}
    (hm : m ∉ monSet n) : seriesCoeff Γ n f a b m y = 0 := by
  unfold seriesCoeff
  simp [termFun_coeff_eq_zero Γ n f _ y a b hm]

/-- The global two-form `E` (`ar:eq:Eseries`) with polynomial coefficients: its `(a, b)` component
at `y` is the homogeneous polynomial of degree `n` whose coefficients are those of the series. -/
def seriesForm (y : Fin 5 → ℝ) (a b : Fin 5) : MvPolynomial (Fin 3) ℂ :=
  ∑ m ∈ monSet n, monomial m (seriesCoeff Γ n f a b m y)

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem coeff_seriesForm (m : Fin 3 →₀ ℕ) (y : Fin 5 → ℝ) (a b : Fin 5) :
    (seriesForm Γ n f y a b).coeff m = seriesCoeff Γ n f a b m y := by
  unfold seriesForm
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ monSet n
  · rw [Finset.sum_eq_single m (fun m' _ hne => by simp [hne]) (fun h => absurd hm h)]
    simp
  · rw [Finset.sum_eq_zero fun m' hm' => by
      have : m' ≠ m := fun h => hm (h ▸ hm')
      simp [this]]
    exact (seriesCoeff_eq_zero Γ n f y a b hm).symm

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
theorem seriesForm_isHomogeneous (y : Fin 5 → ℝ) (a b : Fin 5) :
    MvPolynomial.IsHomogeneous (seriesForm Γ n f y a b) n := by
  intro d hd
  by_cases hdm : d ∈ monSet n
  · exact weight_eq_of_mem_monSet hdm
  · exfalso; apply hd; rw [coeff_seriesForm]; exact seriesCoeff_eq_zero Γ n f y a b hdm

end SeriesForm

/-! ### Equivariance of the series under `Γ` -/

theorem formPullback_isHomogeneous {n : ℕ}
    (om : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (hom : ∀ y a b, MvPolynomial.IsHomogeneous (om y a b) n) (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (x : Fin 5 → ℝ) (i j : Fin 5) :
    MvPolynomial.IsHomogeneous (formPullback Φ om x i j) n := by
  unfold formPullback
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ => ?_
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun b _ => ?_
  have := (isHomogeneous_C (Fin 3) (((fderiv ℝ Φ x (Pi.single i 1) a *
    fderiv ℝ Φ x (Pi.single j 1) b : ℝ) : ℂ))).mul (hom (Φ x) a b)
  simpa using this

section Equivariance

open UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
  {F : Type*} [FunLike F ℍ ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]
  (n : ℕ) [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

include Λ

omit [Λ.HasDetOne] in
theorem summable_termFun_val (hn : 4 ≤ n) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a b : Fin 5)
    (m : Fin 3 →₀ ℕ) : Summable (fun c : PlaneCoset Γ => termFun Γ n f c a b m y) := by
  obtain ⟨b', hb, hbd⟩ := exists_summable_jet_bound Γ Λ n f hn (isCompact_singleton (x := y))
    (Set.singleton_subset_iff.2 hy) 0 a b m
  refine Summable.of_norm_bounded hb fun c => ?_
  have := hbd c y rfl
  simpa using this

omit [Λ.IsArithmetic] in
theorem termFun_eq_cosetTerm (hLevi : LeviIn Γ Λ) {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) (c : PlaneCoset Γ) :
    termFun Γ n f c i j m x = cosetTerm Γ Λ n f hLevi hx i j m c := by
  conv_rhs => rw [← Quotient.out_eq c]
  rfl

omit [Λ.HasDetOne] in
theorem summable_coeff_pullback (hn : 4 ≤ n) {Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)} {x : Fin 5 → ℝ}
    (hΦ : Φ x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    Summable (fun c : PlaneCoset Γ => (formPullback Φ (fun y a b =>
      summandPoly n (hfun f) (realMat (Quotient.out c).1) y a b) x i j).coeff m) := by
  simp_rw [coeff_formPullback]
  unfold scalarPullback
  refine summable_sum fun a _ => summable_sum fun b _ => ?_
  exact (summable_termFun_val Γ Λ n f hn hΦ a b m).mul_left _

omit [Λ.HasDetOne] in
theorem coeff_pullback_series (hn : 4 ≤ n) {Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)} {x : Fin 5 → ℝ}
    (hΦ : Φ x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    (formPullback Φ (seriesForm Γ n f) x i j).coeff m =
      ∑' c : PlaneCoset Γ, (formPullback Φ (fun y a b =>
        summandPoly n (hfun f) (realMat (Quotient.out c).1) y a b) x i j).coeff m := by
  simp_rw [coeff_formPullback, coeff_seriesForm]
  unfold scalarPullback
  have h1 : ∀ a b : Fin 5, ((fderiv ℝ Φ x (Pi.single i 1) a * fderiv ℝ Φ x (Pi.single j 1) b : ℝ) : ℂ) *
      seriesCoeff Γ n f a b m (Φ x) = ∑' c : PlaneCoset Γ,
      ((fderiv ℝ Φ x (Pi.single i 1) a * fderiv ℝ Φ x (Pi.single j 1) b : ℝ) : ℂ) *
        (summandPoly n (hfun f) (realMat (Quotient.out c).1) (Φ x) a b).coeff m := by
    intro a b
    unfold seriesCoeff termFun
    exact tsum_mul_left.symm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h1 a b]
  have h2 : ∀ a b : Fin 5, Summable (fun c : PlaneCoset Γ =>
      ((fderiv ℝ Φ x (Pi.single i 1) a * fderiv ℝ Φ x (Pi.single j 1) b : ℝ) : ℂ) *
        (summandPoly n (hfun f) (realMat (Quotient.out c).1) (Φ x) a b).coeff m) :=
    fun a b => (summable_termFun_val Γ Λ n f hn hΦ a b m).mul_left _
  beta_reduce
  rw [Finset.sum_congr rfl fun a _ => (Summable.tsum_finsetSum (fun b _ => h2 a b)).symm]
  exact (Summable.tsum_finsetSum fun a _ => summable_sum fun b _ => h2 a b).symm

omit [Λ.IsArithmetic] in
theorem coeff_rho_pullback_term (hLevi : LeviIn Γ Λ) (δ : Γ) {x : Fin 5 → ℝ} (hx : x ∈ Omega)
    (i j : Fin 5) (m : Fin 3 →₀ ℕ) (c : PlaneCoset Γ) :
    (SeedC3.rho (realMat δ.1)⁻¹ (formPullback (planeAct (realMat δ.1)) (fun y a b =>
      summandPoly n (hfun f) (realMat (Quotient.out c).1) y a b) x i j)).coeff m =
      termFun Γ n f (cosetMulR Γ δ c) i j m x := by
  rw [← summandPoly_mul_eq n (hfun f) (det_realMat _) (det_realMat δ.1) hx i j, ← realMat_mul,
    termFun_eq_cosetTerm Γ Λ n f hLevi hx i j m (cosetMulR Γ δ c)]
  conv_rhs => rw [← Quotient.out_eq c]
  rfl

/-- **Equivariance of the series.** For `δ ∈ Γ` and `x ∈ Ω`,
`ρ(δ)⁻¹ δ^* E = E` at `x`. -/
theorem seriesForm_equivariant (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) (δ : Γ) {x : Fin 5 → ℝ}
    (hx : x ∈ Omega) (i j : Fin 5) :
    SeedC3.rho (realMat δ.1)⁻¹ (formPullback (planeAct (realMat δ.1)) (seriesForm Γ n f) x i j) =
      seriesForm Γ n f x i j := by
  have hd := det_realMat δ.1
  have hΦ := planeAct_mem hd hx
  refine MvPolynomial.ext _ _ fun m => ?_
  have hQ := formPullback_isHomogeneous (n := n) _ (fun y a b => seriesForm_isHomogeneous Γ n f y a b)
    (planeAct (realMat δ.1)) x i j
  rw [coeff_rho_expansion hQ, coeff_seriesForm]
  simp_rw [coeff_pullback_series Γ Λ n f hn hΦ i j]
  have hPc : ∀ c : PlaneCoset Γ, MvPolynomial.IsHomogeneous (formPullback (planeAct (realMat δ.1))
      (fun y a b => summandPoly n (hfun f) (realMat (Quotient.out c).1) y a b) x i j) n :=
    fun c => formPullback_isHomogeneous _ (fun y a b =>
      summandPoly_isHomogeneous n (hfun f) (det_realMat _) y a b) _ x i j
  have hs : ∀ m' ∈ monSet n, Summable (fun c : PlaneCoset Γ => (formPullback (planeAct (realMat δ.1))
      (fun y a b => summandPoly n (hfun f) (realMat (Quotient.out c).1) y a b) x i j).coeff m' *
        (SeedC3.rho (realMat δ.1)⁻¹ (monomial m' 1)).coeff m) := fun m' _ =>
    (summable_coeff_pullback Γ Λ n f hn hΦ i j m').mul_right _
  calc _ = ∑ m' ∈ monSet n, ∑' c : PlaneCoset Γ, (formPullback (planeAct (realMat δ.1))
        (fun y a b => summandPoly n (hfun f) (realMat (Quotient.out c).1) y a b) x i j).coeff m' *
          (SeedC3.rho (realMat δ.1)⁻¹ (monomial m' 1)).coeff m :=
        Finset.sum_congr rfl fun m' _ => tsum_mul_right.symm
    _ = ∑' c : PlaneCoset Γ, ∑ m' ∈ monSet n, (formPullback (planeAct (realMat δ.1))
        (fun y a b => summandPoly n (hfun f) (realMat (Quotient.out c).1) y a b) x i j).coeff m' *
          (SeedC3.rho (realMat δ.1)⁻¹ (monomial m' 1)).coeff m := (Summable.tsum_finsetSum hs).symm
    _ = ∑' c : PlaneCoset Γ, (SeedC3.rho (realMat δ.1)⁻¹ (formPullback (planeAct (realMat δ.1))
        (fun y a b => summandPoly n (hfun f) (realMat (Quotient.out c).1) y a b) x i j)).coeff m :=
        tsum_congr fun c => (coeff_rho_expansion (hPc c) _ m).symm
    _ = ∑' c : PlaneCoset Γ, termFun Γ n f (cosetMulR Γ δ c) i j m x :=
        tsum_congr fun c => coeff_rho_pullback_term Γ Λ n f hLevi δ hx i j m c
    _ = seriesCoeff Γ n f i j m x :=
        (cosetMulREquiv Γ δ).tsum_eq (fun c => termFun Γ n f c i j m x)

end Equivariance

end TernaryPeriodPolynomials.Argument.ConvergenceC4
