module

public import TernaryPeriodPolynomials.Polynomial.Integral
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodPrimitive
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

@[expose] public section


open MvPolynomial

noncomputable section

namespace TernaryPoly

local notation "BP" => MvPolynomial (Fin 2) ℚ

private def bs (a b : BP) : BP →ₐ[ℚ] BP := bind₁ ![a,b]

private theorem bs_comp (a b c d g : BP) :
    bs a b (bs c d g) = bs (bs a b c) (bs a b d) g := by
  simp only [bs, bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem bs_id (g : BP) : bs (X 0) (X 1) g = g := by
  have h : (![X 0, X 1] : Fin 2 → BP) = X := by
    funext i
    fin_cases i <;> rfl
  simp [bs, h]

/-- The binary polynomial chain rule, with both coordinate derivatives explicit. -/
theorem binary_pderiv_substitution (g a b : BP) (i : Fin 2) :
    pderiv i (bind₁ ![a,b] g) =
      bind₁ ![a,b] (pderiv 0 g) * pderiv i a +
        bind₁ ![a,b] (pderiv 1 g) * pderiv i b := by
  induction g using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    ring
  | mul_X p j hp =>
    fin_cases j <;> simp [map_mul, map_add, hp] <;> ring

private theorem finSuccEquiv_binary_X_one :
    finSuccEquiv ℚ 1 (X (1 : Fin 2)) = Polynomial.C (X (0 : Fin 1)) :=
  finSuccEquiv_X_succ (R := ℚ) (n := 1) (j := 0)

private theorem finSuccEquiv_binary_pderiv (g : BP) :
    finSuccEquiv ℚ 1 (pderiv 0 g) = Polynomial.derivative (finSuccEquiv ℚ 1 g) := by
  induction g using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    fin_cases i <;> simp [map_mul, map_add, hp, Polynomial.derivative_mul,
      finSuccEquiv_X_zero, finSuccEquiv_binary_X_one, mul_comm]

private theorem finSuccEquiv_binary_axis (g : BP) :
    finSuccEquiv ℚ 1 (bs 0 (X 1) g) =
      Polynomial.C ((finSuccEquiv ℚ 1 g).coeff 0) := by
  induction g using MvPolynomial.induction_on with
  | C r => simp [bs, finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.coeff_add]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    fin_cases i <;> simp [bs, finSuccEquiv_X_zero, finSuccEquiv_binary_X_one]

private theorem binary_first_derivative_rigidity (g : BP)
    (hd : pderiv 0 g = 0) (haxis : bs 0 (X 1) g = 0) : g = 0 := by
  have hder : Polynomial.derivative (finSuccEquiv ℚ 1 g) = 0 := by
    rw [← finSuccEquiv_binary_pderiv, hd, map_zero]
  have hconstant : (finSuccEquiv ℚ 1 g).coeff 0 = 0 := by
    have h := congrArg (finSuccEquiv ℚ 1) haxis
    rw [finSuccEquiv_binary_axis, map_zero (finSuccEquiv ℚ 1)] at h
    exact Polynomial.C_injective (by simpa only [map_zero] using h)
  apply (finSuccEquiv ℚ 1).injective
  rw [map_zero]
  apply polynomial_eq_of_derivative_eq_of_coeff_zero_eq
  · simpa using hder
  · simpa using hconstant

/-- A zero diagonal derivative and zero value on one transverse axis force a binary polynomial to vanish. -/
theorem binary_diagonal_derivative_rigidity (g : BP)
    (hd : pderiv 0 g + pderiv 1 g = 0)
    (haxis : bind₁ (![X 0, 0] : Fin 2 → BP) g = 0) : g = 0 := by
  let r := bs (X 0+X 1) (X 0) g
  have hrder : pderiv 0 r = 0 := by
    dsimp [r, bs]
    rw [binary_pderiv_substitution]
    simp only [map_add, pderiv_X_self, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0),
      add_zero, mul_one]
    rw [← map_add, hd, map_zero]
  have hraxis : bs 0 (X 1) r = 0 := by
    dsimp [r]
    rw [bs_comp]
    simp only [bs, map_add, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_add]
    have h := congrArg (bs (X 1) (X 0)) haxis
    change bs (X 1) (X 0) (bs (X 0) 0 g) = _ at h
    rw [bs_comp] at h
    simpa [bs] using h
  have hr : r = 0 := binary_first_derivative_rigidity r hrder hraxis
  have h := congrArg (bs (X 1) (X 0-X 1)) hr
  dsimp [r] at h
  rw [bs_comp] at h
  have he : bs (X 1) (X 0-X 1) (X 0+X 1) = X 0 := by
    simp [bs]
  rw [he] at h
  simp only [bs, bind₁_X_right, Matrix.cons_val_zero, map_zero] at h
  exact (bs_id g).symm.trans h

private def diagonal (g : BP) : BP := pderiv 0 g + pderiv 1 g

private theorem diagonal_bs (g a b : BP) :
    diagonal (bs a b g) = bs a b (pderiv 0 g) * diagonal a +
      bs a b (pderiv 1 g) * diagonal b := by
  simp only [diagonal, bs]
  rw [binary_pderiv_substitution, binary_pderiv_substitution]
  ring

private theorem alternating_binary_first_partial {p q : BP}
    (hq : bind₁ ![X 1, X 0] q = -q) (hder : pderiv 1 q = -p) :
    pderiv 0 q = bs (X 1) (X 0) p := by
  have h := congrArg (pderiv (0 : Fin 2)) hq
  rw [binary_pderiv_substitution] at h
  simp [hder] at h
  exact h.symm

private theorem alternating_binary_diagonal_zero {q : BP}
    (hq : bind₁ ![X 1, X 0] q = -q) : bs (X 0) (X 0) q = 0 := by
  have h := congrArg (bs (X 0) (X 0)) hq
  change bs (X 0) (X 0) (bs (X 1) (X 0) q) = _ at h
  rw [bs_comp] at h
  have hn : bs (X 0) (X 0) q = -bs (X 0) (X 0) q := by
    simpa [bs] using h
  have ht : (2 : ℚ) • bs (X 0) (X 0) q = 0 := by
    simpa only [two_smul] using eq_neg_iff_add_eq_zero.mp hn
  have hz := congrArg (fun v : BP => (2 : ℚ)⁻¹ • v) ht
  simpa only [inv_smul_smul₀ (two_ne_zero : (2 : ℚ) ≠ 0), smul_zero] using hz

/-- The symmetry and primitive difference equations force the exact binary period equation. -/
theorem binary_period_equation (p h q : BP)
    (hqswap : bind₁ ![X 1, X 0] q = -q)
    (hpeven : bind₁ ![-X 0, X 1] p = p)
    (hqder : pderiv 1 q = -p)
    (hhswap : bind₁ ![X 1, X 0] h = h)
    (hdiff : bind₁ ![X 0-X 1, X 1] p - p = h)
    (hqaxis : bind₁ (![X 0, 0] : Fin 2 → BP) q = 0) :
    q - bind₁ ![X 0-X 1, X 1] q - bind₁ ![X 0, X 0-X 1] q = 0 := by
  have hqx := alternating_binary_first_partial hqswap hqder
  have hqdiag := alternating_binary_diagonal_zero hqswap
  have hleft : diagonal (bs (X 0-X 1) (X 1) q) =
      bs (X 0-X 1) (X 1) (pderiv 1 q) := by
    rw [diagonal_bs]
    simp [diagonal]
  have hright : diagonal (bs (X 0) (X 0-X 1) q) =
      bs (X 0) (X 0-X 1) (pderiv 0 q) := by
    rw [diagonal_bs]
    simp [diagonal]
  have hpeven' : bs (X 1-X 0) (X 0) p = bs (X 0-X 1) (X 0) p := by
    have ht := congrArg (bs (X 0-X 1) (X 0)) hpeven
    change bs (X 0-X 1) (X 0) (bs (-X 0) (X 1) p) = _ at ht
    rw [bs_comp] at ht
    simpa [bs] using ht
  have hdiff' : bs (X 0-X 1) (X 0) p - bs (X 1) (X 0) p = h := by
    have ht := congrArg (bs (X 1) (X 0)) hdiff
    change bs (X 1) (X 0) (bs (X 0-X 1) (X 1) p-p) = _ at ht
    rw [map_sub, bs_comp, show bs (X 1) (X 0) h = h from hhswap] at ht
    have ht' : bs (X 1-X 0) (X 0) p - bs (X 1) (X 0) p = h := by
      simpa [bs] using ht
    rwa [hpeven'] at ht'
  apply binary_diagonal_derivative_rigidity
  · change diagonal (q - bs (X 0-X 1) (X 1) q - bs (X 0) (X 0-X 1) q) = 0
    have hd : diagonal (q - bs (X 0-X 1) (X 1) q - bs (X 0) (X 0-X 1) q) =
        diagonal q - diagonal (bs (X 0-X 1) (X 1) q) -
          diagonal (bs (X 0) (X 0-X 1) q) := by
      simp only [diagonal, map_sub]
      abel
    rw [hd, hleft, hright]
    change (pderiv 0 q + pderiv 1 q) - bs (X 0-X 1) (X 1) (pderiv 1 q) -
      bs (X 0) (X 0-X 1) (pderiv 0 q) = 0
    rw [hqx, hqder, map_neg, bs_comp]
    have ht : bs (X 0) (X 0-X 1) (X 1) = X 0-X 1 := by simp [bs]
    have hu : bs (X 0) (X 0-X 1) (X 0) = X 0 := by simp [bs]
    rw [ht, hu]
    calc
      (bs (X 1) (X 0) p + -p) - -bs (X 0-X 1) (X 1) p -
          bs (X 0-X 1) (X 0) p =
          (bs (X 0-X 1) (X 1) p-p) -
            (bs (X 0-X 1) (X 0) p-bs (X 1) (X 0) p) := by abel
      _ = h-h := by rw [show bs (X 0-X 1) (X 1) p-p=h from hdiff, hdiff']
      _ = 0 := sub_self h
  · change bs (X 0) 0 (q - bs (X 0-X 1) (X 1) q - bs (X 0) (X 0-X 1) q) = 0
    rw [map_sub, map_sub, bs_comp, bs_comp]
    have ht : bs (X 0) 0 (X 0-X 1) = X 0 := by simp [bs]
    have hu : bs (X 0) 0 (X 1) = 0 := by simp [bs]
    have hv : bs (X 0) 0 (X 0) = X 0 := by simp [bs]
    rw [ht, hu, hv, show bs (X 0) 0 q=0 from hqaxis, hqdiag]
    simp

/-- The explicit binary primitive satisfies the period equation whenever its source has the
symmetric difference relation. -/
theorem binaryPeriodPrimitive_period_equation (p h : BP) (n : ℕ)
    (hp : p.IsHomogeneous n)
    (hrotation : binaryRotation (pderiv 0 p) = pderiv 0 p)
    (hpeven : bind₁ ![-X 0, X 1] p = p)
    (hpodd : bind₁ ![X 0, -X 1] p = -p)
    (hpaxis : bind₁ (![0, X 1] : Fin 2 → BP) p = 0)
    (hhswap : bind₁ ![X 1, X 0] h = h)
    (hdiff : bind₁ ![X 0-X 1, X 1] p - p = h) :
    binaryPeriodPrimitive n p - bind₁ ![X 0-X 1, X 1] (binaryPeriodPrimitive n p) -
      bind₁ ![X 0, X 0-X 1] (binaryPeriodPrimitive n p) = 0 :=
  binary_period_equation p h (binaryPeriodPrimitive n p)
    (binaryPeriodPrimitive_swap n hpodd) hpeven (binaryPeriodPrimitive_pderiv hp hrotation)
    hhswap hdiff (binaryPeriodPrimitive_axis_second n hpaxis)

end TernaryPoly
