module

public import TernaryPeriodPolynomials.Polynomial.IntegralTaylor.Tail
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Ring.Hom.InjSurj

@[expose] public section

open MvPolynomial
open scoped BigOperators
noncomputable section
namespace TernaryPoly.BivariateTaylorTruncation

variable {R : Type*} [CommRing R]

/-- Translate the two coordinates by fixed elements of the coefficient ring. -/
def shiftedTaylor (Q : MvPolynomial (Fin 2) R) (rb rc : R) : MvPolynomial (Fin 2) R :=
  bind₁ ![X 0 + C rb, X 1 + C rc] Q

/-- The finitely supported exponent associated to a pair of Taylor orders. -/
def binaryExponent (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

@[simp] theorem binaryExponent_zero (i j : ℕ) : binaryExponent i j 0 = i := by
  simp [binaryExponent]
@[simp] theorem binaryExponent_one (i j : ℕ) : binaryExponent i j 1 = j := by
  simp [binaryExponent]

theorem binaryExponent_eta (d : Fin 2 →₀ ℕ) : binaryExponent (d 0) (d 1) = d := by
  ext i
  fin_cases i <;> simp

/-- The six orders retained by the modulo-eight Taylor reduction. -/
def lowExponent : Fin 6 → (Fin 2 →₀ ℕ) :=
  ![binaryExponent 0 0, binaryExponent 1 0, binaryExponent 0 1,
    binaryExponent 2 0, binaryExponent 1 1, binaryExponent 0 2]

theorem lowExponent_injective : Function.Injective lowExponent := by
  intro i j h
  have h₀ := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
  have h₁ := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
  clear h
  fin_cases i <;> fin_cases j <;> simp_all [lowExponent]

def lowSupport : Finset (Fin 2 →₀ ℕ) := Finset.univ.image lowExponent

theorem mem_lowSupport (d : Fin 2 →₀ ℕ) : d ∈ lowSupport ↔ d 0+d 1 < 3 := by
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    fin_cases i <;> norm_num [lowExponent, binaryExponent]
  · intro h
    have hcases : (d 0 = 0 ∧ d 1 = 0) ∨ (d 0 = 1 ∧ d 1 = 0) ∨
        (d 0 = 0 ∧ d 1 = 1) ∨ (d 0 = 2 ∧ d 1 = 0) ∨
        (d 0 = 1 ∧ d 1 = 1) ∨ (d 0 = 0 ∧ d 1 = 2) := by omega
    rcases hcases with h|h|h|h|h|h
    all_goals rw [← binaryExponent_eta d, h.1, h.2]
    all_goals simp [lowSupport, lowExponent, Fin.exists_fin_succ]

/-- Evaluating the translated polynomial at the coordinate differences reverses the shift. -/
theorem shiftedTaylor_eval (Q : MvPolynomial (Fin 2) R) (rb rc : R)
    (B D : Polynomial R) :
    eval₂ Polynomial.C ![B-Polynomial.C rb, D-Polynomial.C rc] (shiftedTaylor Q rb rc) =
      eval₂ Polynomial.C ![B,D] Q := by
  change (eval₂Hom Polynomial.C ![B-Polynomial.C rb, D-Polynomial.C rc])
    (bind₁ ![X 0+C rb, X 1+C rc] Q) = _
  rw [eval₂Hom_bind₁]
  have he : (fun i => (eval₂Hom Polynomial.C ![B-Polynomial.C rb, D-Polynomial.C rc])
      (![X 0+C rb, X 1+C rc] i)) = ![B,D] := by
    funext i
    fin_cases i <;> simp
  rw [he]
  rfl

/-- Exact finite Taylor expansion, valid for every degree and arbitrary commutative coefficients. -/
theorem exact_taylor_expansion (Q : MvPolynomial (Fin 2) R) (rb rc : R)
    (B D : Polynomial R) :
    eval₂ Polynomial.C ![B,D] Q =
      ∑ d ∈ (shiftedTaylor Q rb rc).support,
        Polynomial.C ((shiftedTaylor Q rb rc).coeff d) *
          (B-Polynomial.C rb)^(d 0) * (D-Polynomial.C rc)^(d 1) := by
  rw [← shiftedTaylor_eval Q rb rc B D, eval₂_eq']
  apply Finset.sum_congr rfl
  intro d hd
  simp [Fin.prod_univ_two, mul_assoc]

/-- The constant Taylor coefficient is evaluation at the fixed reference pair. -/
theorem shiftedTaylor_coeff_zero (Q : MvPolynomial (Fin 2) R) (rb rc : R) :
    (shiftedTaylor Q rb rc).coeff 0 = eval ![rb,rc] Q := by
  rw [← constantCoeff_eq, ← eval_zero]
  change (eval₂Hom (RingHom.id R) (0 : Fin 2 → R))
    (bind₁ ![X 0+C rb, X 1+C rc] Q) = _
  rw [eval₂Hom_bind₁]
  have he : (fun i => (eval₂Hom (RingHom.id R) (0 : Fin 2 → R))
      (![X 0+C rb, X 1+C rc] i)) = ![rb,rc] := by
    funext i
    fin_cases i <;> simp
  rw [he]
  rfl

/-- Partial derivatives commute with translation by fixed coefficient data. -/
theorem pderiv_shiftedTaylor (Q : MvPolynomial (Fin 2) R) (rb rc : R) (i : Fin 2) :
    pderiv i (shiftedTaylor Q rb rc) = shiftedTaylor (pderiv i Q) rb rc := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [shiftedTaylor]
  | add p q hp hq => simp_all [shiftedTaylor, map_add]
  | mul_X p j hp =>
    fin_cases i <;> fin_cases j <;>
      simp_all [shiftedTaylor, map_mul, pderiv_X]

/-- Both first Taylor coefficients are the evaluated partial derivatives. -/
theorem shiftedTaylor_coeff_single (Q : MvPolynomial (Fin 2) R) (rb rc : R) (i : Fin 2) :
    (shiftedTaylor Q rb rc).coeff (Finsupp.single i 1) =
      eval ![rb,rc] (pderiv i Q) := by
  have h := shiftedTaylor_coeff_zero (pderiv i Q) rb rc
  rw [← pderiv_shiftedTaylor, coeff_pderiv] at h
  simpa using h

/-- Three linear derivative records; references remain inside the coefficient ring. -/
def record (F : Polynomial R) (t : R) (k : Fin 3) : Polynomial R →+ R where
  toFun p := ![Polynomial.eval t (F*p),
    2*Polynomial.eval t (Polynomial.derivative (F*p)),
    2*Polynomial.eval t (Polynomial.derivative (Polynomial.derivative (F*p)))] k
  map_zero' := by fin_cases k <;> simp
  map_add' p q := by
    fin_cases k <;> simp [mul_add, Polynomial.derivative_add, Polynomial.eval_add]

theorem record_C_mul (F p : Polynomial R) (t a : R) (k : Fin 3) :
    record F t k (Polynomial.C a*p) = a*record F t k p := by
  have he : F*(Polynomial.C a*p) = Polynomial.C a*(F*p) := by ring
  fin_cases k
  · change Polynomial.eval t (F*(Polynomial.C a*p)) = a*Polynomial.eval t (F*p)
    rw [he]
    simp
  · change 2*Polynomial.eval t (Polynomial.derivative (F*(Polynomial.C a*p))) =
      a*(2*Polynomial.eval t (Polynomial.derivative (F*p)))
    rw [he, Polynomial.derivative_C_mul]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    ring
  · change 2*Polynomial.eval t (Polynomial.derivative (Polynomial.derivative (F*(Polynomial.C a*p)))) =
      a*(2*Polynomial.eval t (Polynomial.derivative (Polynomial.derivative (F*p))))
    rw [he, Polynomial.derivative_C_mul, Polynomial.derivative_C_mul]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    ring

/-- Split an arbitrary finitely supported coefficient expression into the six low orders and its tail. -/
theorem sum_sub_six_eq_tail {A : Type*} [AddCommGroup A]
    (P : MvPolynomial (Fin 2) R) (a : (Fin 2 →₀ ℕ) → A)
    (ha : ∀ d, P.coeff d = 0 → a d = 0) :
    (∑ d ∈ P.support, a d) - (∑ k : Fin 6, a (lowExponent k)) =
      ∑ d ∈ P.support with 3 ≤ d 0+d 1, a d := by
  classical
  have hlo : (∑ d ∈ P.support with d 0+d 1 < 3, a d) = ∑ d ∈ lowSupport, a d := by
    apply Finset.sum_subset
    · intro d hd
      exact (mem_lowSupport d).mpr (Finset.mem_filter.mp hd).2
    · intro d hd hn
      apply ha
      have hn' : d ∉ P.support := by
        intro hs
        exact hn (Finset.mem_filter.mpr ⟨hs, (mem_lowSupport d).mp hd⟩)
      simpa using hn'
  have him : (∑ d ∈ lowSupport, a d) = ∑ k : Fin 6, a (lowExponent k) := by
    exact Finset.sum_image (fun i _ j _ h => lowExponent_injective h)
  have hsplit := Finset.sum_filter_add_sum_filter_not P.support (fun d => d 0+d 1 < 3) a
  simp only [not_lt] at hsplit
  rw [hlo, him] at hsplit
  rw [← hsplit]
  abel

/-- One weighted monomial in the exact Taylor support expansion. -/
def taylorTerm (Q : MvPolynomial (Fin 2) R) (rb rc : R)
    (B D : Polynomial R) (d : Fin 2 →₀ ℕ) : Polynomial R :=
  Polynomial.C ((shiftedTaylor Q rb rc).coeff d) *
    (B-Polynomial.C rb)^(d 0) * (D-Polynomial.C rc)^(d 1)

theorem taylorTerm_record (Q : MvPolynomial (Fin 2) R) (rb rc : R)
    (F B D : Polynomial R) (t : R) (k : Fin 3) (d : Fin 2 →₀ ℕ) :
    record F t k (taylorTerm Q rb rc B D d) =
      (shiftedTaylor Q rb rc).coeff d * record F t k
        (IntegralTaylorTail.powerTerm (B-Polynomial.C rb) (D-Polynomial.C rc) (d 0) (d 1)) := by
  unfold taylorTerm IntegralTaylorTail.powerTerm
  rw [mul_assoc, record_C_mul]

/-- Every omitted monomial is a multiple of eight in each genuine polynomial derivative record. -/
theorem taylorTerm_tail_dvd (Q : MvPolynomial (Fin 2) R) (rb rc : R)
    (F B D : Polynomial R) (t : R)
    (hB : (2 : R) ∣ Polynomial.eval t B-rb) (hD : (2 : R) ∣ Polynomial.eval t D-rc)
    (k : Fin 3) (d : Fin 2 →₀ ℕ) (hd : 3 ≤ d 0+d 1) :
    (8 : R) ∣ record F t k (taylorTerm Q rb rc B D d) := by
  rw [taylorTerm_record]
  apply dvd_mul_of_dvd_right
  have h := IntegralTaylorTail.polynomial_tail_record_divisibility
    (Polynomial.evalRingHom t) F (B-Polynomial.C rb) (D-Polynomial.C rc)
    (by simpa using hB) (by simpa using hD) (d 0) (d 1) hd
  fin_cases k
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- Full-polynomial Taylor truncation modulo eight in all three records, with no degree bound. -/
theorem record_taylor_truncation (Q : MvPolynomial (Fin 2) R) (rb rc : R)
    (F B D : Polynomial R) (t : R)
    (hB : (2 : R) ∣ Polynomial.eval t B-rb) (hD : (2 : R) ∣ Polynomial.eval t D-rc)
    (k : Fin 3) :
    (8 : R) ∣ record F t k (eval₂ Polynomial.C ![B,D] Q) -
      ∑ l : Fin 6, (shiftedTaylor Q rb rc).coeff (lowExponent l) *
        record F t k (IntegralTaylorTail.powerTerm
          (B-Polynomial.C rb) (D-Polynomial.C rc) ((lowExponent l) 0) ((lowExponent l) 1)) := by
  have hs := sum_sub_six_eq_tail (shiftedTaylor Q rb rc)
    (fun d => record F t k (taylorTerm Q rb rc B D d))
    (by intro d hd; simp [taylorTerm, hd])
  rw [exact_taylor_expansion Q rb rc B D, map_sum]
  change (8 : R) ∣ (∑ d ∈ (shiftedTaylor Q rb rc).support,
    record F t k (taylorTerm Q rb rc B D d)) - _
  simp_rw [← taylorTerm_record]
  rw [hs]
  apply Finset.dvd_sum
  intro d hd
  exact taylorTerm_tail_dvd Q rb rc F B D t hB hD k d (Finset.mem_filter.mp hd).2

end TernaryPoly.BivariateTaylorTruncation
