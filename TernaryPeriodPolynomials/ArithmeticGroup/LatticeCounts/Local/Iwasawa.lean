module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Polynomial.Monomial
public import Mathlib.Analysis.Normed.MulAction
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
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.ZMod
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Peel
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Local lattice reduction over `ℚ_[p]`

Formalized by Claude Haiku 5.5.

For a nonzero determinant `g ∈ M₂(ℚ_[p])` we produce a rational matrix `q` whose
denominators are powers of `p`, whose determinant is a power of `p`, and such that
`q * g ∈ GL₂(ℤ_[p])`.  The proof is elementary: complete the bottom row of `g` to a
matrix `K ∈ GL₂(ℤ_[p])` making `g * K` upper triangular, then correct the upper entry
by a `ℤ[1/p]`-approximation.
-/

open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LocalIwasawa

variable {p : ℕ} [Fact p.Prime]

/-- `GL₂(ℤ_[p])` inside `M₂(ℚ_[p])`: integral entries and unit determinant. -/
def PInt (M : Matrix (Fin 2) (Fin 2) ℚ_[p]) : Prop :=
  (∀ i j, ‖M i j‖ ≤ 1) ∧ ‖M.det‖ = 1

lemma hp0 : (p : ℚ_[p]) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

lemma hpR : (1 : ℝ) < p := by
  exact_mod_cast (Fact.out : p.Prime).one_lt

lemma norm_add_le_one' {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (Padic.nonarchimedean a b).trans (max_le ha hb)

lemma norm_mul_le_one' {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hb

lemma pInt_mul {M N : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hM : PInt M) (hN : PInt N) :
    PInt (M * N) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact norm_add_le_one' (norm_mul_le_one' (hM.1 i 0) (hN.1 0 j))
      (norm_mul_le_one' (hM.1 i 1) (hN.1 1 j))
  · rw [Matrix.det_mul, norm_mul, hM.2, hN.2, mul_one]

lemma pInt_det_ne_zero {M : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hM : PInt M) : M.det ≠ 0 := by
  intro h
  have := hM.2
  rw [h, norm_zero] at this
  exact zero_ne_one this

lemma pInt_inv {K : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hK : PInt K) : PInt K⁻¹ := by
  have hadj : ∀ i j, ‖K.adjugate i j‖ ≤ 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two, hK.1]
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    apply norm_mul_le_one'
    · rw [norm_inv, hK.2, inv_one]
    · exact hadj i j
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, hK.2, inv_one]

/-- Completing a nonzero bottom row `(c, d)` to `K ∈ GL₂(ℤ_[p])` with `c K₀₀ + d K₁₀ = 0`. -/
lemma exists_completion (c d : ℚ_[p]) (hcd : c ≠ 0 ∨ d ≠ 0) :
    ∃ K : Matrix (Fin 2) (Fin 2) ℚ_[p], PInt K ∧ c * K 0 0 + d * K 1 0 = 0 ∧
      c * K 0 1 + d * K 1 1 ≠ 0 := by
  by_cases h : ‖d‖ ≤ ‖c‖
  · have hc : c ≠ 0 := by
      rcases hcd with h1 | h1
      · exact h1
      · intro hc
        have hd0 : ‖d‖ = 0 := le_antisymm (by simpa [hc] using h) (norm_nonneg _)
        exact h1 (norm_eq_zero.mp hd0)
    have hdc : ‖d‖ / ‖c‖ ≤ 1 := div_le_one_of_le₀ h (norm_nonneg _)
    have key : c * (d / c) = d := by field_simp
    refine ⟨!![d / c, -1; -1, 0], ⟨fun i j => ?_, ?_⟩, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [hdc]
    · simp [Matrix.det_fin_two_of]
    · simp [key]
    · simp [hc]
  · push Not at h
    have hd : d ≠ 0 := by
      intro hd0; rw [hd0, norm_zero] at h; exact absurd h (not_lt.mpr (norm_nonneg _))
    have hcd' : ‖c‖ / ‖d‖ ≤ 1 := div_le_one_of_le₀ h.le (norm_nonneg _)
    have key : d * (-c / d) = -c := by field_simp
    refine ⟨!![1, 0; -c / d, 1], ⟨fun i j => ?_, ?_⟩, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [hcd']
    · simp [Matrix.det_fin_two_of]
    · simp [key]
    · simp [hd]

/-- Bounding a `ℚ_[p]`-element by a power of `p` times it is integral. -/
lemma exists_bound (w : ℚ_[p]) : ∃ M : ℕ, ‖(p : ℚ_[p]) ^ M * w‖ ≤ 1 := by
  by_cases hw : w = 0
  · exact ⟨0, by simp [hw]⟩
  refine ⟨(-w.valuation).toNat, ?_⟩
  have hM : -w.valuation ≤ (((-w.valuation).toNat : ℕ) : ℤ) := Int.self_le_toNat _
  have hpR0 : (p : ℝ) ≠ 0 := (zero_lt_one.trans hpR).ne'
  rw [norm_mul, norm_pow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hw]
  have h2 : ((p : ℝ)⁻¹) ^ (-w.valuation).toNat = (p : ℝ) ^ (-(((-w.valuation).toNat : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [h2, ← zpow_add₀ hpR0]
  exact zpow_le_one_of_nonpos₀ hpR.le (by linarith)

/-- `ℤ[1/p]` is dense in `ℚ_[p]`: every element is approximated by `n / p^k`. -/
lemma exists_approx (w : ℚ_[p]) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℤ) (k : ℕ), ‖(n : ℚ_[p]) / (p : ℚ_[p]) ^ k - w‖ < ε := by
  obtain ⟨M, hM⟩ := exists_bound (p := p) w
  let x : ℤ_[p] := ⟨(p : ℚ_[p]) ^ M * w, hM⟩
  have hpM : (p : ℚ_[p]) ^ M ≠ 0 := pow_ne_zero _ hp0
  have hnpos : 0 < ‖(p : ℚ_[p]) ^ M‖ := norm_pos_iff.mpr hpM
  obtain ⟨n, hn⟩ := (PadicInt.denseRange_intCast (p := p)).exists_dist_lt x
    (mul_pos hε hnpos)
  have hn' : ‖(p : ℚ_[p]) ^ M * w - n‖ < ε * ‖(p : ℚ_[p]) ^ M‖ := by
    have h1 := hn
    rw [dist_eq_norm, PadicInt.norm_def] at h1
    exact h1
  refine ⟨n, M, ?_⟩
  have e : (n : ℚ_[p]) / (p : ℚ_[p]) ^ M - w
      = ((p : ℚ_[p]) ^ M)⁻¹ * ((n : ℚ_[p]) - (p : ℚ_[p]) ^ M * w) := by
    field_simp
  rw [e, norm_mul, norm_inv, norm_sub_rev, inv_mul_lt_iff₀ hnpos]
  linarith [hn']

lemma exists_zpow_mul_pow (e : ℤ) : ∃ (n : ℤ) (k : ℕ), (p : ℚ) ^ e * (p : ℚ) ^ k = n := by
  have hp0Q : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℕ, e + ((-e).toNat : ℤ) = (m : ℤ) := ⟨(e + ((-e).toNat : ℤ)).toNat, by omega⟩
  refine ⟨(p : ℤ) ^ m, (-e).toNat, ?_⟩
  rw [← zpow_natCast, ← zpow_add₀ hp0Q, hm, zpow_natCast]
  push_cast
  rfl

/-- The local reduction at `p`: a rational `q` with `p`-power denominators and `p`-power
determinant such that `q * g` is in `GL₂(ℤ_[p])`. -/
theorem exists_local_reduction (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) (hg : g.det ≠ 0) :
    ∃ q : Matrix (Fin 2) (Fin 2) ℚ, (∃ e : ℤ, q.det = (p : ℚ) ^ e) ∧
      (∀ i j, ∃ (n : ℤ) (k : ℕ), q i j * (p : ℚ) ^ k = n) ∧
      PInt (q.map (algebraMap ℚ ℚ_[p]) * g) := by
  have hcd : g 1 0 ≠ 0 ∨ g 1 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    rw [Matrix.det_fin_two, h.1, h.2]
    ring
  obtain ⟨K, hK, hbl, hbr⟩ := exists_completion (g 1 0) (g 1 1) hcd
  have hdetK : K.det ≠ 0 := pInt_det_ne_zero hK
  set g' : Matrix (Fin 2) (Fin 2) ℚ_[p] := g * K with hg'
  have hg'10 : g' 1 0 = 0 := by
    simp only [hg', Matrix.mul_apply, Fin.sum_univ_two]
    exact hbl
  have hdetg' : g'.det ≠ 0 := by
    rw [hg', Matrix.det_mul]; exact mul_ne_zero hg hdetK
  have hδ : g' 1 1 ≠ 0 := by
    intro h0
    apply hdetg'
    rw [Matrix.det_fin_two, hg'10, h0]
    ring
  have hα : g' 0 0 ≠ 0 := by
    intro h0
    apply hdetg'
    rw [Matrix.det_fin_two, hg'10, h0]
    ring
  set α := g' 0 0 with hαdef
  set β := g' 0 1 with hβdef
  set δ := g' 1 1 with hδdef
  -- rational powers of `p` that normalise the diagonal
  set a := α.valuation with ha
  set b := δ.valuation with hb
  set q11 : ℚ := (p : ℚ) ^ (-a) with hq11def
  set q22 : ℚ := (p : ℚ) ^ (-b) with hq22def
  have hq11 : algebraMap ℚ ℚ_[p] q11 = (p : ℚ_[p]) ^ (-a) := by
    simp [hq11def]
  have hq22 : algebraMap ℚ ℚ_[p] q22 = (p : ℚ_[p]) ^ (-b) := by
    simp [hq22def]
  have hpR0 : (p : ℝ) ≠ 0 := (zero_lt_one.trans hpR).ne'
  have hp0Q : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hαn : ‖α‖ = (p : ℝ) ^ (-a) := Padic.norm_eq_zpow_neg_valuation hα
  have hδn : ‖δ‖ = (p : ℝ) ^ (-b) := Padic.norm_eq_zpow_neg_valuation hδ
  have hq11α : ‖algebraMap ℚ ℚ_[p] q11 * α‖ = 1 := by
    rw [hq11, norm_mul, Padic.norm_p_zpow, neg_neg, hαn, ← zpow_add₀ hpR0]; simp
  have hq22δ : ‖algebraMap ℚ ℚ_[p] q22 * δ‖ = 1 := by
    rw [hq22, norm_mul, Padic.norm_p_zpow, neg_neg, hδn, ← zpow_add₀ hpR0]; simp
  set w : ℚ_[p] := -(algebraMap ℚ ℚ_[p] q11 * β) / δ with hw
  have hεpos : 0 < ‖δ‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hδ)
  obtain ⟨n, k, hnk⟩ := exists_approx (p := p) w hεpos
  set t : ℚ := (n : ℚ) / (p : ℚ) ^ k with ht_def
  have ht : algebraMap ℚ ℚ_[p] t = (n : ℚ_[p]) / (p : ℚ_[p]) ^ k := by
    simp [ht_def]
  have ht_den : t * (p : ℚ) ^ k = n := by
    rw [ht_def]; field_simp
  have hT : ‖algebraMap ℚ ℚ_[p] t - w‖ < ‖δ‖⁻¹ := by rw [ht]; exact hnk
  have hentry : ‖algebraMap ℚ ℚ_[p] q11 * β + algebraMap ℚ ℚ_[p] t * δ‖ ≤ 1 := by
    have hkey : algebraMap ℚ ℚ_[p] q11 * β + algebraMap ℚ ℚ_[p] t * δ
        = δ * (algebraMap ℚ ℚ_[p] t - w) := by
      rw [hw]; field_simp; ring
    rw [hkey, norm_mul]
    calc ‖δ‖ * ‖algebraMap ℚ ℚ_[p] t - w‖ ≤ ‖δ‖ * ‖δ‖⁻¹ :=
          mul_le_mul_of_nonneg_left hT.le (norm_nonneg _)
      _ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.mpr hδ)
  let Qm : Matrix (Fin 2) (Fin 2) ℚ := !![q11, t; 0, q22]
  have hdetQ : (Qm.map (algebraMap ℚ ℚ_[p])).det = algebraMap ℚ ℚ_[p] q11 * algebraMap ℚ ℚ_[p] q22 := by
    simp [Qm, Matrix.det_fin_two]
  have hdetg' : g'.det = α * δ := by
    rw [Matrix.det_fin_two, hg'10]; ring
  have e00 : (Qm.map (algebraMap ℚ ℚ_[p]) * g') 0 0 = algebraMap ℚ ℚ_[p] q11 * α := by
    simp [Qm, Matrix.mul_apply, Fin.sum_univ_two, hg'10, α]
  have e01 : (Qm.map (algebraMap ℚ ℚ_[p]) * g') 0 1
      = algebraMap ℚ ℚ_[p] q11 * β + algebraMap ℚ ℚ_[p] t * δ := by
    simp [Qm, Matrix.mul_apply, Fin.sum_univ_two, β, δ]
  have e10 : (Qm.map (algebraMap ℚ ℚ_[p]) * g') 1 0 = 0 := by
    simp [Qm, Matrix.mul_apply, Fin.sum_univ_two, hg'10]
  have e11 : (Qm.map (algebraMap ℚ ℚ_[p]) * g') 1 1 = algebraMap ℚ ℚ_[p] q22 * δ := by
    simp [Qm, Matrix.mul_apply, Fin.sum_univ_two, δ]
  have hQg' : PInt (Qm.map (algebraMap ℚ ℚ_[p]) * g') := by
    refine ⟨Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩, ?_⟩
    · rw [e00]; exact hq11α.le
    · rw [e01]; exact hentry
    · rw [e10]; simp
    · rw [e11]; exact hq22δ.le
    · rw [Matrix.det_mul, hdetQ, hdetg']
      have e : algebraMap ℚ ℚ_[p] q11 * algebraMap ℚ ℚ_[p] q22 * (α * δ)
          = (algebraMap ℚ ℚ_[p] q11 * α) * (algebraMap ℚ ℚ_[p] q22 * δ) := by ring
      rw [e, norm_mul, hq11α, hq22δ, mul_one]
  have hKinv : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetK)
  have hQg : Qm.map (algebraMap ℚ ℚ_[p]) * g = Qm.map (algebraMap ℚ ℚ_[p]) * g' * K⁻¹ := by
    simp only [hg', Matrix.mul_assoc, hKinv, Matrix.mul_one]
  refine ⟨Qm, ⟨-a + -b, ?_⟩, ?_, ?_⟩
  · simp [Qm, Matrix.det_fin_two, zpow_add₀ hp0Q, q11, q22]
  · intro i j
    fin_cases i <;> fin_cases j
    · simpa [Qm, q11] using exists_zpow_mul_pow (p := p) (-a)
    · exact ⟨n, k, by simpa [Qm] using ht_den⟩
    · exact ⟨0, 0, by simp [Qm]⟩
    · simpa [Qm, q22] using exists_zpow_mul_pow (p := p) (-b)
  · rw [hQg]
    exact pInt_mul hQg' (pInt_inv hK)

end TernaryPeriodPolynomials.Argument.LatticeCounts.LocalIwasawa
