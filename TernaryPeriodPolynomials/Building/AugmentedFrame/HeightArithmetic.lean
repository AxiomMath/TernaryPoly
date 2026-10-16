module

public import TernaryPeriodPolynomials.Building.OrientedChain.ListChains
public import Mathlib.Data.Int.DivMod
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Lean.Meta.Tactic.Rewrite

@[expose] public section


namespace TernaryPoly.AugmentedHeightArithmetic

/-- The carry in Euclidean division of an integer sum by a positive height. -/
def carry (N a b : ℤ) : ℤ := (a+b) / N - a / N - b / N

/-- Every integer has a representative with height in the half-open standard interval. -/
theorem remainder_bounds (N a : ℤ) (hN : 0 < N) :
    0 ≤ a % N ∧ a % N < N :=
  ⟨Int.emod_nonneg a (ne_of_gt hN),Int.emod_lt_of_pos a hN⟩

/-- Subtracting the integral quotient times the chosen height gives the remainder. -/
theorem quotient_sub_eq_remainder (N a : ℤ) : a - (a / N) * N = a % N := by
  have h := Int.emod_add_ediv_mul a N
  omega

/-- The carry is exactly the discrepancy in the three nonnegative remainders. -/
theorem carry_mul (N a b : ℤ) :
    carry N a b * N = a % N + b % N - (a+b) % N := by
  have ha := quotient_sub_eq_remainder N a
  have hb := quotient_sub_eq_remainder N b
  have hab := quotient_sub_eq_remainder N (a+b)
  dsimp [carry]
  nlinarith

/-- For a positive divisor, adding two residues produces either no carry or one carry. -/
theorem carry_zero_or_one (N a b : ℤ) (hN : 0 < N) :
    carry N a b = 0 ∨ carry N a b = 1 := by
  obtain ⟨ha0,haN⟩ := remainder_bounds N a hN
  obtain ⟨hb0,hbN⟩ := remainder_bounds N b hN
  obtain ⟨hab0,habN⟩ := remainder_bounds N (a+b) hN
  have hc := carry_mul N a b
  have hlo : 0 ≤ carry N a b := by nlinarith
  have hhi : carry N a b ≤ 1 := by nlinarith
  omega

/-- Carrying is equivalent to crossing the positive-height threshold. -/
theorem carry_eq_one_iff (N a b : ℤ) (hN : 0 < N) :
    carry N a b = 1 ↔ N ≤ a % N + b % N := by
  have hc := carry_mul N a b
  obtain ⟨hab0,habN⟩ := remainder_bounds N (a+b) hN
  obtain hc0 | hc1 := carry_zero_or_one N a b hN
  · rw [hc0]
    rw [hc0,zero_mul] at hc
    omega
  · rw [hc1]
    rw [hc1,one_mul] at hc
    omega

/-- In the carrying case neither input remainder vanishes. -/
theorem carrying_remainders_pos (N a b : ℤ) (hN : 0 < N)
    (hc : carry N a b = 1) : 0 < a % N ∧ 0 < b % N := by
  have hsum := (carry_eq_one_iff N a b hN).mp hc
  obtain ⟨ha0,haN⟩ := remainder_bounds N a hN
  obtain ⟨hb0,hbN⟩ := remainder_bounds N b hN
  omega

/-- The extra vertex used to subdivide a carrying triangle has strictly smaller absolute height. -/
theorem carrying_center_bounds (N a b : ℤ) (hN : 0 < N)
    (hc : carry N a b = 1) :
    -N < a % N - N ∧ a % N - N < 0 ∧ |a % N - N| < N := by
  have hp := (carrying_remainders_pos N a b hN hc).1
  have hu := (remainder_bounds N a hN).2
  constructor
  · omega
  constructor
  · omega
  rw [abs_of_neg (by omega : a % N - N < 0)]
  omega

/-- The corrected additive relation between reduced heights in the carrying case. -/
theorem carrying_remainder_sum (N a b : ℤ) (hc : carry N a b = 1) :
    (a+b) % N = a % N + b % N - N := by
  have h := carry_mul N a b
  rw [hc,one_mul] at h
  omega

/-- The ordinary additive relation between reduced heights in the no-carry case. -/
theorem no_carry_remainder_sum (N a b : ℤ) (hc : carry N a b = 0) :
    (a+b) % N = a % N + b % N := by
  have h := carry_mul N a b
  rw [hc,zero_mul] at h
  omega

open OrientedListChains

/-- The oriented three-triangle replacement used in a carrying retraction. -/
noncomputable def subdividedTriangle {V : Type*} (a b c t : V) : Chain V :=
  simplex [t,b,c] + simplex [a,t,c] + simplex [a,b,t]

/-- The three triangles have exactly the original oriented boundary. No geometry is assumed here. -/
theorem boundary_subdividedTriangle {V : Type*} (a b c t : V) :
    boundary (subdividedTriangle a b c t) = boundary (simplex [a,b,c]) := by
  simp only [subdividedTriangle,map_add,boundary_cons,boundary_nil,map_zero,
    map_sub,cons_simplex]
  have h := simplex_swap_eq_neg t b ([] : List V)
  rw [h]
  abel

end TernaryPoly.AugmentedHeightArithmetic
