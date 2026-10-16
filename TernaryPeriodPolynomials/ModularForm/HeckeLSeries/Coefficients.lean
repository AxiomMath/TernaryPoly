module

public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section

noncomputable section
namespace TernaryPoly.BinaryHeckeCoefficients

/-- The exact prime Hecke relation implies a recurrence after adjoining any residual factor. -/
theorem recurrence_mul (a : ℕ → ℂ) (c : Nat.Primes → ℂ)
    (h : ∀ p : Nat.Primes, ∀ n : ℕ,
      a (p.val*n) + c p * (if p.val ∣ n then a (n/p.val) else 0) = a p.val * a n)
    (p : Nat.Primes) (r n : ℕ) :
    a (p.val^(r+2)*n) = a p.val * a (p.val^(r+1)*n) - c p * a (p.val^r*n) := by
  have hp := (Nat.irreducible_iff_nat_prime _).mp p.property
  have hdvd : p.val ∣ p.val^(r+1)*n := by
    use p.val^r*n
    ring
  have hdiv : p.val^(r+1)*n/p.val = p.val^r*n := by
    rw [show p.val^(r+1)*n = (p.val^r*n)*p.val by ring]
    exact Nat.mul_div_cancel _ hp.pos
  have hmul : p.val*(p.val^(r+1)*n) = p.val^(r+2)*n := by ring
  have he := h p (p.val^(r+1)*n)
  rw [ite_eq_left hdvd, hdiv, hmul] at he
  linear_combination he

/-- The ordinary second-order prime-power recurrence. -/
theorem prime_power_recurrence (a : ℕ → ℂ) (c : Nat.Primes → ℂ)
    (h : ∀ p : Nat.Primes, ∀ n : ℕ,
      a (p.val*n) + c p * (if p.val ∣ n then a (n/p.val) else 0) = a p.val * a n)
    (p : Nat.Primes) (r : ℕ) :
    a (p.val^(r+2)) = a p.val * a (p.val^(r+1)) - c p * a (p.val^r) := by
  simpa only [mul_one] using recurrence_mul a c h p r 1

/-- A prime-power factor separates from every residual argument coprime to that prime. -/
theorem prime_power_mul (a : ℕ → ℂ) (c : Nat.Primes → ℂ) (ha1 : a 1 = 1)
    (h : ∀ p : Nat.Primes, ∀ n : ℕ,
      a (p.val*n) + c p * (if p.val ∣ n then a (n/p.val) else 0) = a p.val * a n)
    (p : Nat.Primes) (n : ℕ) (hn : ¬ p.val ∣ n) (r : ℕ) :
    a (p.val^r*n) = a (p.val^r)*a n := by
  induction r using Nat.twoStepInduction with
  | zero => simp [ha1]
  | one => simpa [hn] using h p n
  | more r ih0 ih1 =>
      rw [recurrence_mul a c h, prime_power_recurrence a c h, ih0, ih1]
      ring

/-- The prime Hecke relations force coprime multiplicativity for all natural indices. -/
theorem coprime_multiplicative (a : ℕ → ℂ) (c : Nat.Primes → ℂ)
    (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (h : ∀ p : Nat.Primes, ∀ n : ℕ,
      a (p.val*n) + c p * (if p.val ∣ n then a (n/p.val) else 0) = a p.val * a n)
    (m n : ℕ) (hmn : m.Coprime n) : a (m*n) = a m * a n := by
  induction m using Nat.recOnPrimePow generalizing n with
  | zero => simp [ha0]
  | one => simp [ha1]
  | @prime_pow_mul m p r hp hpm hr ih =>
      let pp : Nat.Primes := ⟨p, (Nat.irreducible_iff_nat_prime _).mpr hp⟩
      have hpn : ¬ p ∣ n := by
        intro hpn
        have hd : p ∣ p^r*m := dvd_mul_of_dvd_left (dvd_pow_self p (Nat.ne_zero_of_lt hr)) m
        have hc := hmn.of_dvd_left hd
        exact hp.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) hpn)
      have hpmn : ¬ p ∣ m*n := by
        intro hd
        exact (hp.dvd_mul.mp hd).elim hpm hpn
      have hmn' : m.Coprime n := hmn.of_dvd_left (dvd_mul_left m (p^r))
      rw [mul_assoc, prime_power_mul a c ha1 h pp (m*n) hpmn,
        prime_power_mul a c ha1 h pp m hpm, ih n hmn']
      ring

end TernaryPoly.BinaryHeckeCoefficients
