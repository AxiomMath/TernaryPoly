module

public import TernaryPeriodPolynomials.Polynomial.PeriodSubstitution
public import TernaryPeriodPolynomials.Polynomial.Parity

@[expose] public section


/-! # Axis normalization and odd-degree vanishing for full binary periods -/


open MvPolynomial

noncomputable section
namespace TernaryPoly.Paper

variable {R : Type*} [CommRing R]

/-- Binary monomials evaluate as the product of their two coordinate powers. -/
theorem binaryEval_monomial {σ : Type*} (d : Fin 2 →₀ ℕ) (r : R)
    (a b : MvPolynomial σ R) :
    binaryEval (monomial d r) a b = MvPolynomial.C r * a ^ d 0 * b ^ d 1 := by
  classical
  rw [binaryEval, bind₁_monomial]
  have hprod : (∏ i ∈ d.support, (![a,b] i) ^ d i) = a ^ d 0 * b ^ d 1 := by
    rw [← Finsupp.prod, Finsupp.prod_fintype]
    · simp [Fin.prod_univ_two]
    · intro i
      simp
  rw [hprod]
  ring

/-- The total degree of a binary exponent is the sum of its entries. -/
theorem binary_degree (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  change d.sum (fun _ k => k) = _
  rw [Finsupp.sum_fintype]
  · simp [Fin.sum_univ_two]
  · intro i
    rfl

/-- Homogeneity identifies the exact coefficient on the horizontal axis. -/
theorem homogeneous_axis_second {q : Binary R} {n : ℕ} (hq : q.IsHomogeneous n)
    {σ : Type*} (a : MvPolynomial σ R) :
    binaryEval q a 0 = MvPolynomial.C (q.coeff (Finsupp.single 0 n)) * a ^ n := by
  classical
  have hm (d : Fin 2 →₀ ℕ) (hd : d ∈ q.support) (hne : d ≠ Finsupp.single 0 n) :
      binaryEval (monomial d (q.coeff d)) a 0 = 0 := by
    have hdg : d.degree = n := (hq.degree_eq_sum_deg_support hd).symm
    have h₁ : d 1 ≠ 0 := by
      intro hz
      apply hne
      have h₀ : d 0 = n := by rw [binary_degree, hz, add_zero] at hdg; exact hdg
      ext i
      fin_cases i <;> simp [h₀, hz]
    rw [binaryEval_monomial, zero_pow h₁, mul_zero]
  calc
    binaryEval q a 0 = ∑ d ∈ q.support, binaryEval (monomial d (q.coeff d)) a 0 := by
      unfold binaryEval
      rw [← map_sum, ← as_sum]
    _ = binaryEval (monomial (Finsupp.single 0 n) (q.coeff (Finsupp.single 0 n))) a 0 := by
      apply Finset.sum_eq_single
      · intro d hd hne
        exact hm d hd hne
      · intro hn
        rw [notMem_support_iff.mp hn, monomial_zero, binaryEval_zero]
    _ = _ := by simp [binaryEval_monomial]

/-- The exact axis coboundary removed in the normalized even period map. -/
def axisCoboundary (R : Type*) [CommRing R] (n : ℕ) : Binary R := X 0 ^ n - X 1 ^ n

/-- Normalize a homogeneous period by its literal horizontal-axis coefficient. -/
def normalizePeriod (n : ℕ) (q : Binary R) : Binary R :=
  q - q.coeff (Finsupp.single 0 n) • axisCoboundary R n

/-- The axis coboundary satisfies both full period identities in even degree. -/
theorem axisCoboundary_identities (R : Type*) [CommRing R] {n : ℕ} (hn : Even n) :
    PeriodIdentities (axisCoboundary R n) := by
  constructor
  · simp [axisCoboundary, hn.neg_pow]
  · simp only [axisCoboundary, map_sub, map_pow, bind₁_X_right,
      Matrix.cons_val_zero, Matrix.cons_val_one, hn.neg_pow]
    rw [show (X 1-X 0 : Binary R) = -(X 0-X 1) by ring, hn.neg_pow]
    ring

/-- Removing an axis coboundary preserves both period identities. -/
theorem normalizePeriod_identities {q : Binary R} {n : ℕ} (hn : Even n)
    (hq : PeriodIdentities q) : PeriodIdentities (normalizePeriod n q) := by
  have hc := axisCoboundary_identities R hn
  constructor
  · simp only [normalizePeriod, Algebra.smul_def, algebraMap_eq, map_sub, map_mul, bind₁_C_right]
    linear_combination hq.1 - MvPolynomial.C (q.coeff (Finsupp.single 0 n)) * hc.1
  · simp only [normalizePeriod, Algebra.smul_def, algebraMap_eq, map_sub, map_mul, bind₁_C_right]
    linear_combination hq.2 - MvPolynomial.C (q.coeff (Finsupp.single 0 n)) * hc.2

/-- The normalization is horizontal-axis zero in positive degree. -/
theorem normalizePeriod_axis_second {q : Binary R} {n : ℕ} (hn : n ≠ 0)
    (hq : q.IsHomogeneous n) :
    bind₁ (![X 0, 0] : Fin 2 → Binary R) (normalizePeriod n q) = 0 := by
  change binaryEval (normalizePeriod n q) (X 0) 0 = 0
  simp only [normalizePeriod, binaryEval, map_sub, map_smul]
  rw [show bind₁ (![X 0, 0] : Fin 2 → Binary R) q = MvPolynomial.C (q.coeff (Finsupp.single 0 n)) * X 0 ^ n
    from homogeneous_axis_second hq (X 0)]
  simp [axisCoboundary, hn, Algebra.smul_def]

/-- The other axis follows from the literal two-term period relation. -/
theorem PeriodIdentities.axis_first_of_axis_second {q : Binary R}
    (hq : PeriodIdentities q) (haxis : bind₁ (![X 0, 0] : Fin 2 → Binary R) q = 0) :
    bind₁ (![0, X 1] : Fin 2 → Binary R) q = 0 := by
  have h := hq.eval_two_term (X 1 : Binary R) 0
  have h₀ := congrArg (fun p : Binary R => binaryEval p (X 1 : Binary R) 0) haxis
  simp [binaryEval, bind₁_bind₁, bind_vec2] at h₀
  change binaryEval q (X 1 : Binary R) 0 = 0 at h₀
  rw [h₀, zero_add, neg_zero] at h
  exact h

/-- Positive-even normalization produces a full normalized period. -/
theorem normalizePeriod_relations {q : Binary R} {n : ℕ} (hn : n ≠ 0) (he : Even n)
    (hh : q.IsHomogeneous n) (hq : PeriodIdentities q) :
    PeriodRelations (normalizePeriod n q) := by
  have hi := normalizePeriod_identities he hq
  have ha := normalizePeriod_axis_second hn hh
  exact ⟨hi.axis_first_of_axis_second ha, ha, hi⟩

/-- The horizontal coefficient of the coboundary is exactly one in positive degree. -/
theorem coeff_axisCoboundary (n : ℕ) (hn : n ≠ 0) :
    (axisCoboundary R n).coeff (Finsupp.single 0 n) = 1 := by
  have hne : (Finsupp.single 1 n : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 n := by
    intro h
    have he := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
    simp at he
    exact hn he.symm
  simp [axisCoboundary, coeff_X_pow, hne]

/-- The coefficient functional detects a normalized polynomial's missing axis term. -/
theorem PeriodRelations.axis_coefficient_eq_zero {q : Binary R} (hq : PeriodRelations q)
    (n : ℕ) : q.coeff (Finsupp.single 0 n) = 0 := by
  have h := congrArg (·.coeff (Finsupp.single 0 n)) hq.axis_second
  have hc : (bind₁ (![X 0,0] : Fin 2 → Binary R) q).coeff (Finsupp.single 0 n) =
      q.coeff (Finsupp.single 0 n) := by
    clear hq h
    classical
    induction q using MvPolynomial.induction_on' with
    | monomial d r =>
      rw [show bind₁ (![X 0,0] : Fin 2 → Binary R) (monomial d r) =
        MvPolynomial.C r * X 0 ^ d 0 * 0 ^ d 1 from binaryEval_monomial d r (X 0) 0]
      by_cases hd : d 1 = 0
      · have hd' : d = Finsupp.single 0 (d 0) := by
          ext i
          fin_cases i <;> simp [hd]
        rw [hd, pow_zero, mul_one, C_mul_X_pow_eq_monomial, ← hd']
      · have hne : d ≠ Finsupp.single 0 n := by
          intro he
          apply hd
          simp [he]
        simp [hd, hne]
    | add p r hp hr => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hr]
  rw [hc, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
  exact h

/-- Normalization fixes every already normalized period. -/
theorem normalizePeriod_eq_self {q : Binary R} (hq : PeriodRelations q) (n : ℕ) :
    normalizePeriod n q = q := by
  simp [normalizePeriod, hq.axis_coefficient_eq_zero n]

/-- Every scalar axis coboundary is removed exactly. -/
theorem normalizePeriod_smul_axisCoboundary (n : ℕ) (hn : n ≠ 0) (c : R) :
    normalizePeriod n (c • axisCoboundary R n) = 0 := by
  simp [normalizePeriod, coeff_axisCoboundary n hn]

/-- Normalization preserves the homogeneous degree. -/
theorem normalizePeriod_homogeneous {q : Binary R} {n : ℕ} (hq : q.IsHomogeneous n) :
    (normalizePeriod n q).IsHomogeneous n := by
  apply hq.sub
  simpa [Algebra.smul_def, axisCoboundary] using
    ((isHomogeneous_X_pow 0 n).sub (isHomogeneous_X_pow 1 n)).C_mul
      (q.coeff (Finsupp.single 0 n))

/-- Evenness in the first variable survives the normalization in even degree. -/
theorem normalizePeriod_even {q : Binary R} {n : ℕ} (hn : Even n)
    (hq : bind₁ ![-X 0,X 1] q = q) :
    bind₁ ![-X 0,X 1] (normalizePeriod n q) = normalizePeriod n q := by
  simp only [normalizePeriod, map_sub, map_smul, hq]
  congr 2
  simp [axisCoboundary, hn.neg_pow]

/-- Odd-degree full periods vanish over characteristic-zero fields. -/
theorem period_odd_eq_zero {F : Type*} [Field F] [CharZero F] {q : Binary F} {n : ℕ}
    (hh : q.IsHomogeneous n) (hq : PeriodIdentities q) (hn : Odd n) : q = 0 := by
  have h := homogeneous_bind_smul hh (-1 : F)
  have hv : (fun i : Fin 2 => (-1 : F) • (X i : Binary F)) = ![-X 0, -X 1] := by
    funext i
    fin_cases i <;> simp
  rw [hv, hq.neg_neg, hn.neg_one_pow, neg_one_smul] at h
  exact CharZero.eq_neg_self_iff.mp h

/-- Normalized degree-zero periods vanish over every coefficient ring. -/
theorem period_zero_eq_zero {q : Binary R} (hh : q.IsHomogeneous 0)
    (hq : PeriodRelations q) : q = 0 := by
  have hc : q = MvPolynomial.C (q.coeff 0) :=
    (homogeneousComponent_eq_self hh).symm.trans (homogeneousComponent_zero _)
  have ha := hq.axis_second
  rwa [hc, bind₁_C_right, ← hc] at ha

end TernaryPoly.Paper
