module

public import Mathlib
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Primitive
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.CyclicCount

@[expose] public section


/-!
# The shell-sum identity and the shell count

Formalized by Claude Haiku 5.5.

Part A (algebra). With `t = p^{-(k-2)}`, `q = p^{k-1}`, `u = p^{k-2}` in a field, and `H(T) = (1 - aT + qT²)⁻¹`:
`c_p := 1 + (1 - p⁻¹) ((1 - u t²) H(t) - 1)` equals `(1 - a t/p + q t²/p²)/(1 - a t + q t²)`.
This is `shell_identity_of_relations` (abstract relations `u t = 1`, `q t = p`) and
`local_factor_closed_form` (the zpow instance, with the closed form written in exponents of `p`).
The target closed form is the right-hand side of `unramified_local_factor`
(`Revision/Targets/UnramifiedFactor.lean`); the series identity that makes the left side of
`unramified_local_factor` equal `c_p` is the Hecke generating-function step inside
`Revision/Proofs/CuspForms/UnramifiedFactorProof.lean` and is cited, not re-derived here.

Part B (shell count). `Nat.card (PrimPt p r) = (p^r + p^(r-1)) (p^r - p^(r-1))` for `r ≥ 1`,
obtained by partitioning primitive pairs by `lamST` into cyclic index-`p^r` lattices, each fibre of
size `p^r - p^(r-1)`, and the number of such lattices `p^r + p^(r-1)`.
Also `(p^r + p^(r-1))(p^r - p^(r-1)) = p^(2r) - p^(2r-2)`.
-/

namespace TernaryPeriodPolynomials.Argument.LatticeCounts

/-! ## Part A: algebra -/

theorem shell_identity_of_relations {K : Type*} [Field K] {P a q t u : K}
    (hP : P ≠ 0) (hut : u * t = 1) (hqt : q * t = P)
    (hD : 1 - a * t + q * t ^ 2 ≠ 0) :
    1 + (1 - P⁻¹) * ((1 - u * t ^ 2) * (1 - a * t + q * t ^ 2)⁻¹ - 1) =
      (1 - a * t / P + q * t ^ 2 / P ^ 2) / (1 - a * t + q * t ^ 2) := by
  have hut2 : u * t ^ 2 = t := by linear_combination t * hut
  have hqt2 : q * t ^ 2 = P * t := by linear_combination t * hqt
  rw [hut2, hqt2]
  rw [hqt2] at hD
  set D := 1 - a * t + P * t with hDdef
  field_simp
  rw [hDdef]
  ring

/-- The zpow form: `t = p^{-(k-2)}`, `q = p^{k-1}`, `u = p^{k-2}`, with the closed form in
exponents of `p`. -/
theorem local_factor_closed_form {K : Type*} [Field K] {p : K} (hp : p ≠ 0) (a : K) (k : ℤ)
    (hD : 1 - a * p ^ (2 - k) + p ^ (3 - k) ≠ 0) :
    1 + (1 - p⁻¹) * ((1 - p ^ (k - 2) * (p ^ (-(k - 2))) ^ 2) *
        (1 - a * p ^ (-(k - 2)) + p ^ (k - 1) * (p ^ (-(k - 2))) ^ 2)⁻¹ - 1) =
      (1 - a * p ^ (1 - k) + p ^ (1 - k)) / (1 - a * p ^ (2 - k) + p ^ (3 - k)) := by
  have ht : p ^ (-(k - 2)) = p ^ (2 - k) := by congr 1; ring
  have hut : p ^ (k - 2) * p ^ (-(k - 2)) = 1 := by
    rw [← zpow_add₀ hp]; simp
  have hqt : p ^ (k - 1) * p ^ (-(k - 2)) = p := by
    rw [← zpow_add₀ hp]
    have e : k - 1 + -(k - 2) = 1 := by ring
    rw [e, zpow_one]
  have h1 : p ^ (k - 1) * (p ^ (2 - k)) ^ 2 = p ^ (3 - k) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hp]
    congr 1
    push_cast
    ring
  have hA : p ^ (2 - k) / p = p ^ (1 - k) := by
    rw [div_eq_mul_inv, ← zpow_neg_one, ← zpow_add₀ hp]
    congr 1
    ring
  have hB : p ^ (3 - k) / p ^ 2 = p ^ (1 - k) := by
    rw [← zpow_natCast, div_eq_mul_inv, ← zpow_neg, ← zpow_add₀ hp]
    congr 1
    push_cast
    ring
  have hD' : 1 - a * p ^ (-(k - 2)) + p ^ (k - 1) * (p ^ (-(k - 2))) ^ 2 ≠ 0 := by
    rw [ht, h1]
    exact hD
  have key := shell_identity_of_relations (P := p) (a := a) (q := p ^ (k - 1))
    (t := p ^ (-(k - 2))) (u := p ^ (k - 2)) hp hut hqt hD'
  rw [key, ht, h1]
  congr 1
  rw [mul_div_assoc, hA, hB]

/-! ## Part B: the shell count -/

/-- The shell count: primitive pairs are partitioned by their lattice `lamST`, whose fibres have
size `p^r - p^(r-1)` and whose values are the cyclic index-`p^r` lattices, numbering
`p^r + p^(r-1)`. -/
theorem card_shell_primPt (p : ℕ) [hp : Fact p.Prime] {r : ℕ} (hr : 1 ≤ r) :
    Nat.card (PrimPt p r) = (p ^ r + p ^ (r - 1)) * (p ^ r - p ^ (r - 1)) := by
  have hr0 : 0 < r := hr
  let X := {L : AddSubgroup (ℤ × ℤ) // L.index = p ^ r ∧ IsAddCyclic ((ℤ × ℤ) ⧸ L)}
  let f : PrimPt p r → X := fun v =>
    ⟨lamST p r v.1.1 v.1.2, index_and_cyclic_lamST ((mem_primPairs p hr0 _).mp v.2)⟩
  have hfinite : Finite X := by
    apply Nat.finite_of_card_ne_zero
    rw [card_cyclic_index_subgroups (p := p) hr]
    have := pow_pos (Fact.out : p.Prime).pos r
    omega
  have : Fintype X := Fintype.ofFinite X
  have hfib : ∀ L : X, Nat.card {v : PrimPt p r // f v = L} = p ^ r - p ^ (r - 1) := by
    intro L
    have hequiv : Nat.card {v : PrimPt p r // f v = L} =
        Nat.card {v : PrimPt p r // lamST p r v.1.1 v.1.2 = L.1} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun v => Subtype.ext_iff))
    rw [hequiv]
    exact card_fiber_lamST hr0 L.2.1 L.2.2
  calc Nat.card (PrimPt p r)
      = Nat.card (Σ L : X, {v : PrimPt p r // f v = L}) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ L : X, Nat.card {v : PrimPt p r // f v = L} := Nat.card_sigma
    _ = ∑ _L : X, (p ^ r - p ^ (r - 1)) := Finset.sum_congr rfl (fun L _ => hfib L)
    _ = Nat.card X * (p ^ r - p ^ (r - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
    _ = (p ^ r + p ^ (r - 1)) * (p ^ r - p ^ (r - 1)) := by
        rw [card_cyclic_index_subgroups (p := p) hr]

/-- `(p^r + p^(r-1))(p^r - p^(r-1)) = p^(2r) - p^(2r-2)` for `r ≥ 1`. -/
theorem shell_count_eq (p : ℕ) [hp : Fact p.Prime] {r : ℕ} (hr : 1 ≤ r) :
    (p ^ r + p ^ (r - 1)) * (p ^ r - p ^ (r - 1)) = p ^ (2 * r) - p ^ (2 * r - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have e1 : m + 1 - 1 = m := by omega
  have e2 : 2 * (m + 1) - 2 = 2 * m := by omega
  rw [e1, e2]
  have hle : p ^ m ≤ p ^ (m + 1) := Nat.pow_le_pow_right hp.out.pos (by omega)
  have key : (p ^ (m + 1) + p ^ m) * (p ^ (m + 1) - p ^ m) + p ^ (2 * m) = p ^ (2 * (m + 1)) := by
    zify [hle]
    ring
  exact Nat.eq_sub_of_add_eq key

/-- The shell count: `Nat.card (PrimPt p r) = p^(2r) - p^(2r-2)` ( values). -/
theorem card_shell_primPt_eq (p : ℕ) [hp : Fact p.Prime] {r : ℕ} (hr : 1 ≤ r) :
    Nat.card (PrimPt p r) = p ^ (2 * r) - p ^ (2 * r - 2) := by
  rw [card_shell_primPt p hr, shell_count_eq p hr]

end TernaryPeriodPolynomials.Argument.LatticeCounts
