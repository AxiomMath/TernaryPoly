module

public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Closed
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.JetSmooth
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Frozen
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.TermJets
public import TernaryPeriodPolynomials.BoundaryComparison.StokesComparison
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section


/-!
# Closedness of the summands (Appendix C.3, Proposition C.4)

The seed `ω_h` is closed (`seed_closed_equivariant`); the pullback by a smooth map and the coefficient action
`ρ(g)⁻¹` preserve closedness (`closed_scalarPullback`; the coefficients of `ρ(g)⁻¹ P` are fixed
linear combinations of those of the homogeneous polynomial `P`), hence every coefficient form of every
summand `ρ(g)⁻¹ g^* ω_h` is closed at every point of `Ω`: `closedAt_summand_coeff`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff
open Matrix MvPolynomial

/-! ### Closedness of the seed coefficient forms, in `fderiv` form -/

theorem coordPartial_eq_fderiv {f : (Fin 5 → ℝ) → ℂ} {p : Fin 5 → ℝ}
    (hf : DifferentiableAt ℝ f p) (k : Fin 5) :
    coordPartial f k p = fderiv ℝ f p (Pi.single k 1) := by
  unfold coordPartial
  have h1 : HasDerivAt (Function.update p k) (Pi.single k (1 : ℝ)) (p k) :=
    hasDerivAt_update p k (p k)
  have h2 : HasFDerivAt f (fderiv ℝ f p) (Function.update p k (p k)) := by
    rw [Function.update_eq_self]; exact hf.hasFDerivAt
  exact (h2.comp_hasDerivAt (p k) h1).deriv

theorem seedForm_antisymm (n : ℕ) (h : ℂ → ℂ) (y : Fin 5 → ℝ) (a b : Fin 5) :
    seedForm n h y a b = - seedForm n h y b a := by
  unfold seedForm
  rw [← neg_mul, ← map_neg]
  congr 2
  ring

theorem seedCoeff_eq (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (y : Fin 5 → ℝ) (a b : Fin 5) :
    (seedForm n h y a b).coeff m = seedForm0 h y a b * polyCoeff n m (seedRow y) := by
  rw [seedForm_eq_C_mul, seedLinear_eq_sum, coeff_linear_pow]

theorem seedCoeff_differentiableAt (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) {p : Fin 5 → ℝ}
    (hh : DifferentiableAt ℂ h (seedTau p)) (a b : Fin 5) :
    DifferentiableAt ℝ (fun y => (seedForm n h y a b).coeff m) p := by
  have : (fun y => (seedForm n h y a b).coeff m) =
      fun y => seedForm0 h y a b * polyCoeff n m (seedRow y) := funext fun y => seedCoeff_eq n h m y a b
  rw [this]
  have hτ : DifferentiableAt ℝ (fun y => h (seedTau y)) p :=
    (hh.restrictScalars ℝ).comp p (contDiff_seedTau.differentiable (by simp) p)
  have hβ : ∀ c, DifferentiableAt ℝ (fun y => seedBeta y c) p :=
    fun c => ((contDiff_seedBeta_apply c).differentiable (by simp)) p
  have hrow : ContDiff ℝ ∞ (fun y => seedRow y) := contDiff_pi.2 contDiff_seedRow_apply
  refine DifferentiableAt.mul ?_ ?_
  · unfold seedForm0
    exact hτ.mul (((hβ a).mul_const _).sub ((hβ b).mul_const _))
  · exact (((contDiff_polyCoeff n m).comp hrow).differentiable (by simp)) p

theorem seedCoeff_closedAt (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) {p : Fin 5 → ℝ} (hp : 0 < p 3)
    (hh : DifferentiableAt ℂ h (seedTau p)) :
    ClosedAt (fun a b y => (seedForm n h y a b).coeff m) p := by
  intro i j k
  have key := (TernaryPeriodPolynomials.seed_closed_equivariant n h).1 p hp hh m i j k
  rw [coordPartial_eq_fderiv (seedCoeff_differentiableAt n h m hh j k),
    coordPartial_eq_fderiv (seedCoeff_differentiableAt n h m hh i k),
    coordPartial_eq_fderiv (seedCoeff_differentiableAt n h m hh i j)] at key
  exact key

/-! ### The coefficients of a coefficient-action image of a homogeneous polynomial -/

/-- The monomials of degree `n` in three variables. -/
def monSet (n : ℕ) : Finset (Fin 3 →₀ ℕ) := (Finset.univ : Finset (Fin 3)).finsuppAntidiag n

theorem mem_monSet_of_coeff_ne {n : ℕ} {P : MvPolynomial (Fin 3) ℂ} (hP : MvPolynomial.IsHomogeneous P n)
    {m : Fin 3 →₀ ℕ} (hm : P.coeff m ≠ 0) : m ∈ monSet n := by
  have := hP hm
  rw [monSet, Finset.mem_finsuppAntidiag]
  refine ⟨?_, Finset.subset_univ _⟩
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this

theorem coeff_rho_expansion {n : ℕ} {P : MvPolynomial (Fin 3) ℂ} (hP : MvPolynomial.IsHomogeneous P n)
    (G : Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 →₀ ℕ) :
    (SeedC3.rho G P).coeff m =
      ∑ m' ∈ monSet n, P.coeff m' * (SeedC3.rho G (monomial m' 1)).coeff m := by
  have hsum : P = ∑ m' ∈ monSet n, C (P.coeff m') * monomial m' 1 := by
    conv_lhs => rw [P.as_sum]
    have hsub : P.support ⊆ monSet n := fun v hv =>
      mem_monSet_of_coeff_ne hP (MvPolynomial.mem_support_iff.1 hv)
    rw [Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [C_mul_monomial, mul_one]
    · intro v _ hv
      rw [MvPolynomial.notMem_support_iff.1 hv]; simp
  conv_lhs => rw [hsum]
  rw [rho_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [rho_C_mul, MvPolynomial.coeff_C_mul]

theorem seedForm_isHomogeneous (n : ℕ) (h : ℂ → ℂ) (y : Fin 5 → ℝ) (a b : Fin 5) :
    MvPolynomial.IsHomogeneous (seedForm n h y a b) n := by
  rw [seedForm_eq_C_mul, seedLinear_eq_sum]
  have hl : MvPolynomial.IsHomogeneous (∑ k : Fin 3, C (seedRow y k) * (X k : MvPolynomial (Fin 3) ℂ)) 1 :=
    MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => isHomogeneous_C_mul_X _ _
  have := (isHomogeneous_C (Fin 3) (seedForm0 h y a b)).mul (hl.pow n)
  simpa using this

theorem formPullback_seedForm_isHomogeneous (n : ℕ) (h : ℂ → ℂ) (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (x : Fin 5 → ℝ) (i j : Fin 5) : MvPolynomial.IsHomogeneous (formPullback Φ (seedForm n h) x i j) n := by
  unfold formPullback
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ => ?_
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun b _ => ?_
  have := (isHomogeneous_C (Fin 3) (((fderiv ℝ Φ x (Pi.single i 1) a *
    fderiv ℝ Φ x (Pi.single j 1) b : ℝ) : ℂ))).mul (seedForm_isHomogeneous n h (Φ x) a b)
  simpa using this

theorem coeff_formPullback (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ))
    (om : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ) (x : Fin 5 → ℝ) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) :
    (formPullback Φ om x i j).coeff m =
      scalarPullback Φ (fun y a b => (om y a b).coeff m) x i j := by
  unfold formPullback scalarPullback
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]

theorem coeff_summandPoly_expansion (n : ℕ) (h : ℂ → ℂ) (g : Matrix (Fin 3) (Fin 3) ℝ)
    (x : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    (summandPoly n h g x i j).coeff m =
      ∑ m' ∈ monSet n, scalarPullback (planeAct g) (fun y a b => (seedForm n h y a b).coeff m')
        x i j * (SeedC3.rho g⁻¹ (monomial m' 1)).coeff m := by
  unfold summandPoly
  rw [coeff_rho_expansion (formPullback_seedForm_isHomogeneous n h (planeAct g) x i j)]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [coeff_formPullback]

theorem closedAt_finsetSum {ι : Type*} (s : Finset ι) (c : ι → Fin 5 → Fin 5 → (Fin 5 → ℝ) → ℂ)
    (τ : ι → ℂ) (x : Fin 5 → ℝ) (hd : ∀ i ∈ s, ∀ a b, DifferentiableAt ℝ (c i a b) x)
    (hc : ∀ i ∈ s, ClosedAt (c i) x) :
    ClosedAt (fun a b y => ∑ i ∈ s, c i a b y * τ i) x := by
  intro i j k
  have hf : ∀ a b, fderiv ℝ (fun y => ∑ i ∈ s, c i a b y * τ i) x =
      ∑ l ∈ s, τ l • fderiv ℝ (c l a b) x := by
    intro a b
    rw [fderiv_fun_sum fun l hl => (hd l hl a b).mul_const _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [fderiv_mul_const (hd l ‹_› a b)]
  simp only [hf, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun l hl => ?_
  have := hc l hl i j k
  linear_combination τ l * this

/-! ### Closedness of the summands and of the series -/

theorem closedAt_summand_coeff (n : ℕ) (h : ℂ → ℂ) (hd : DifferentiableOn ℂ h upperHalf)
    {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1) {x : Fin 5 → ℝ} (hx : x ∈ Omega)
    (m : Fin 3 →₀ ℕ) :
    ClosedAt (fun a b y => (summandPoly n h g y a b).coeff m) x := by
  have hΦ : ContDiffAt ℝ ∞ (planeAct g) x :=
    (contDiffAt_planeAct hg hx).of_le (by exact_mod_cast le_top)
  have hq'' := planeAct_mem hg hx
  have hh : DifferentiableAt ℂ h (seedTau (planeAct g x)) := by
    refine (hd.differentiableAt (isOpen_upperHalf.mem_nhds ?_))
    show 0 < (seedTau (planeAct g x)).im
    simpa [seedTau] using hq''.1
  have hexp : (fun a b y => (summandPoly n h g y a b).coeff m) = fun a b y =>
      ∑ m' ∈ monSet n, (scalarPullback (planeAct g)
        (fun y a b => (seedForm n h y a b).coeff m') y a b) *
          (SeedC3.rho g⁻¹ (monomial m' 1)).coeff m := by
    funext a b y
    exact coeff_summandPoly_expansion n h g y a b m
  rw [hexp]
  refine closedAt_finsetSum (monSet n) (fun m' a b y => scalarPullback (planeAct g)
    (fun y a b => (seedForm n h y a b).coeff m') y a b)
    (fun m' => (SeedC3.rho g⁻¹ (monomial m' 1)).coeff m) x ?_ ?_
  · intro m' _ a b
    exact differentiableAt_scalarPullback hΦ _ (fun a b => seedCoeff_differentiableAt n h m' hh a b) a b
  · intro m' _
    exact closed_scalarPullback hΦ _ (fun a b => seedCoeff_differentiableAt n h m' hh a b)
      (fun y a b => by rw [seedForm_antisymm n h y a b]; simp)
      (seedCoeff_closedAt n h m' hq''.1 hh)

end TernaryPeriodPolynomials.Argument.ConvergenceC4
