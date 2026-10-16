module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Int.GCD
public import Mathlib.Tactic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Diagonalization of integral `2 × 2` matrices and the transpose Cartan property

Every integral `2 × 2` matrix with nonzero first row is `GL₂(ℤ)`-equivalent (on both sides) to a
diagonal matrix. Consequently `Mᵀ ∈ GL₂(ℤ) · M · GL₂(ℤ)`, which is the Cartan property used by
Gelfand's trick for the spherical Hecke algebra.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open Matrix

namespace TernaryPeriodPolynomials.RepresentationTheory.IntegerCartan

abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ

/-- Two-sided equivalence by unimodular matrices. -/
def Equiv2 (A B : M2) : Prop := ∃ U V : M2, IsUnit U.det ∧ IsUnit V.det ∧ U * A * V = B

theorem Equiv2.refl (A : M2) : Equiv2 A A := ⟨1, 1, by simp, by simp, by simp⟩

theorem Equiv2.trans {A B C : M2} (h₁ : Equiv2 A B) (h₂ : Equiv2 B C) : Equiv2 A C := by
  obtain ⟨U, V, hU, hV, rfl⟩ := h₁
  obtain ⟨U', V', hU', hV', rfl⟩ := h₂
  refine ⟨U' * U, V * V', by rw [det_mul]; exact hU'.mul hU, by rw [det_mul]; exact hV.mul hV', ?_⟩
  simp only [Matrix.mul_assoc]

/-- A column operation making the first row `(gcd a b, 0)`. -/
theorem first_row_gcd (A : M2) (h : A 0 0 ≠ 0 ∨ A 0 1 ≠ 0) :
    ∃ B : M2, Equiv2 A B ∧ B 0 1 = 0 ∧ B 0 0 = (Int.gcd (A 0 0) (A 0 1) : ℤ) := by
  set a := A 0 0
  set b := A 0 1
  set g : ℤ := ((Int.gcd a b : ℕ) : ℤ) with hg
  have hg0 : g ≠ 0 := by
    rw [hg]; exact_mod_cast (Int.gcd_pos_iff.mpr h).ne'
  obtain ⟨a', ha'⟩ : g ∣ a := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ : g ∣ b := Int.gcd_dvd_right a b
  have hbez : a * Int.gcdA a b + b * Int.gcdB a b = g := (Int.gcd_eq_gcd_ab a b).symm
  let V : M2 := !![Int.gcdA a b, -b'; Int.gcdB a b, a']
  have hdet : V.det = 1 := by
    simp only [V, det_fin_two_of]
    have hbez' : g * a' * Int.gcdA a b + g * b' * Int.gcdB a b = g := by
      rw [← ha', ← hb']; exact hbez
    have : g * (Int.gcdA a b * a' + Int.gcdB a b * b') = g * 1 := by
      linear_combination hbez'
    have := mul_left_cancel₀ hg0 this
    linarith
  refine ⟨A * V, ⟨1, V, by simp, by rw [hdet]; exact isUnit_one, by simp⟩, ?_, ?_⟩
  · simp only [V, mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
      empty_val', cons_val_fin_one]
    change a * -b' + b * a' = 0
    rw [ha', hb']; ring
  · simp only [V, mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
      empty_val', cons_val_fin_one]
    change a * Int.gcdA a b + b * Int.gcdB a b = g
    exact hbez

/-- The transpose of the first-column statement. -/
theorem first_col_gcd (A : M2) (h : A 0 0 ≠ 0 ∨ A 1 0 ≠ 0) :
    ∃ B : M2, Equiv2 A B ∧ B 1 0 = 0 ∧ B 0 0 = (Int.gcd (A 0 0) (A 1 0) : ℤ) := by
  obtain ⟨B, ⟨U, V, hU, hV, hB⟩, h01, h00⟩ := first_row_gcd Aᵀ (by simpa using h)
  refine ⟨Bᵀ, ⟨Vᵀ, Uᵀ, by rwa [det_transpose], by rwa [det_transpose], ?_⟩, ?_, ?_⟩
  · rw [← hB]; simp [transpose_mul, Matrix.mul_assoc]
  · simpa using h01
  · simpa using h00

/-- Diagonalization of matrices whose first row is `(g, 0)` with `g ≠ 0`, by strong induction on
`|g|`. -/
theorem diag_of_first_row (n : ℕ) : ∀ A : M2, (A 0 0).natAbs = n → A 0 0 ≠ 0 → A 0 1 = 0 →
    ∃ D : M2, Equiv2 A D ∧ D 0 1 = 0 ∧ D 1 0 = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn h0 h01
    by_cases hdiv : A 0 0 ∣ A 1 0
    · obtain ⟨q, hq⟩ := hdiv
      let U : M2 := !![1, 0; -q, 1]
      refine ⟨U * A, ⟨U, 1, by simp [U, det_fin_two_of], by simp, by simp⟩, ?_, ?_⟩
      · simp [U, mul_apply, Fin.sum_univ_two, h01]
      · simp [U, mul_apply, Fin.sum_univ_two, hq]; ring
    · obtain ⟨B, hAB, hB10, hB00⟩ := first_col_gcd A (Or.inl h0)
      have hgpos : 0 < Int.gcd (A 0 0) (A 1 0) := Int.gcd_pos_iff.mpr (Or.inl h0)
      have hlt : Int.gcd (A 0 0) (A 1 0) < (A 0 0).natAbs := by
        have hle : Int.gcd (A 0 0) (A 1 0) ≤ (A 0 0).natAbs :=
          Nat.le_of_dvd (Int.natAbs_pos.mpr h0) (Int.gcd_dvd_natAbs_left _ _)
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hlt
        · exfalso; apply hdiv
          have : (A 0 0).natAbs ∣ (A 1 0).natAbs := by
            rw [← heq]; exact Int.gcd_dvd_natAbs_right _ _
          exact Int.natAbs_dvd_natAbs.mp this
      obtain ⟨C, hBC, hC01, hC00⟩ := first_row_gcd B (Or.inl (by rw [hB00]; exact_mod_cast hgpos.ne'))
      have hCpos : 0 < Int.gcd (B 0 0) (B 0 1) := Int.gcd_pos_iff.mpr
        (Or.inl (by rw [hB00]; exact_mod_cast hgpos.ne'))
      have hCle : Int.gcd (B 0 0) (B 0 1) ≤ Int.gcd (A 0 0) (A 1 0) := by
        have h1 := Nat.le_of_dvd (Int.natAbs_pos.mpr (by rw [hB00]; exact_mod_cast hgpos.ne'))
          (Int.gcd_dvd_natAbs_left (B 0 0) (B 0 1))
        have h2 : (B 0 0).natAbs = Int.gcd (A 0 0) (A 1 0) := by rw [hB00]; simp
        omega
      obtain ⟨D, hCD, hD01, hD10⟩ := ih (C 0 0).natAbs (by rw [hC00]; simp; omega) C rfl
        (by rw [hC00]; exact_mod_cast hCpos.ne') hC01
      exact ⟨D, (hAB.trans hBC).trans hCD, hD01, hD10⟩

/-- **Diagonalization.** -/
theorem exists_diag (A : M2) (h : A.det ≠ 0) : ∃ D : M2, Equiv2 A D ∧ D 0 1 = 0 ∧ D 1 0 = 0 := by
  have hrow : A 0 0 ≠ 0 ∨ A 0 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    apply h
    rw [det_fin_two, hc.1, hc.2]; ring
  obtain ⟨B, hAB, hB01, hB00⟩ := first_row_gcd A hrow
  have hB0 : B 0 0 ≠ 0 := by rw [hB00]; exact_mod_cast (Int.gcd_pos_iff.mpr hrow).ne'
  obtain ⟨D, hBD, hD⟩ := diag_of_first_row _ B rfl hB0 hB01
  exact ⟨D, hAB.trans hBD, hD⟩

/-- **Transpose Cartan property** for integral `2 × 2` matrices. -/
theorem transpose_equiv (A : M2) (h : A.det ≠ 0) : Equiv2 A Aᵀ := by
  obtain ⟨D, ⟨U, V, hU, hV, hD⟩, hD01, hD10⟩ := exists_diag A h
  have hDT : Dᵀ = D := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hD01, hD10]
  -- `A = U⁻¹ D V⁻¹`, so `Aᵀ = V⁻ᵀ D U⁻ᵀ = (V⁻ᵀ U) A (V U⁻ᵀ)`
  have hUi : U⁻¹ * U = 1 := nonsing_inv_mul U hU
  have hVi : V * V⁻¹ = 1 := mul_nonsing_inv V hV
  have hA : A = U⁻¹ * D * V⁻¹ := by
    rw [← hD]; simp only [Matrix.mul_assoc, hVi, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hUi, Matrix.one_mul]
  refine ⟨V⁻¹ᵀ * U, V * U⁻¹ᵀ, ?_, ?_, ?_⟩
  · rw [det_mul, det_transpose]
    exact (isUnit_nonsing_inv_det V hV).mul hU
  · rw [det_mul, det_transpose]
    exact hV.mul (isUnit_nonsing_inv_det U hU)
  · conv_rhs => rw [hA]
    rw [transpose_mul, transpose_mul, hDT]
    calc V⁻¹ᵀ * U * A * (V * U⁻¹ᵀ) = V⁻¹ᵀ * (U * A * V) * U⁻¹ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = V⁻¹ᵀ * D * U⁻¹ᵀ := by rw [hD]
      _ = V⁻¹ᵀ * (D * U⁻¹ᵀ) := by rw [Matrix.mul_assoc]

/-- Clearing denominators of a rational `2 × 2` matrix. -/
theorem exists_clear_denominators (A : Matrix (Fin 2) (Fin 2) ℚ) :
    ∃ N : ℕ, N ≠ 0 ∧ ∃ M : M2, M.map (Int.cast : ℤ → ℚ) = (N : ℚ) • A := by
  classical
  let N : ℕ := ∏ ij : Fin 2 × Fin 2, (A ij.1 ij.2).den
  have hN : N ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun ij _ => (A ij.1 ij.2).den_nz)
  have hdvd : ∀ i j, (A i j).den ∣ N := fun i j =>
    Finset.dvd_prod_of_mem (fun ij : Fin 2 × Fin 2 => (A ij.1 ij.2).den) (Finset.mem_univ (i, j))
  refine ⟨N, hN, Matrix.of fun i j => (A i j).num * ((N / (A i j).den : ℕ) : ℤ), ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have hq := Rat.mul_den_eq_num (A i j)
  obtain ⟨c, hc⟩ := hdvd i j
  have hdiv : N / (A i j).den = c := by
    rw [hc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (A i j).den_nz)]
  rw [hdiv]
  have hNc : (N : ℚ) = ((A i j).den : ℚ) * c := by exact_mod_cast hc
  rw [hNc]
  push_cast
  rw [← hq]
  ring

/-- **Transpose Cartan property** for rational `2 × 2` matrices. -/
theorem rat_transpose_equiv (A : Matrix (Fin 2) (Fin 2) ℚ) (h : A.det ≠ 0) :
    ∃ U V : M2, IsUnit U.det ∧ IsUnit V.det ∧
      U.map (Int.cast : ℤ → ℚ) * A * V.map (Int.cast : ℤ → ℚ) = Aᵀ := by
  obtain ⟨N, hN, M, hM⟩ := exists_clear_denominators A
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have hcast : ∀ X : M2, (Int.castRingHom ℚ).mapMatrix X = X.map (Int.cast : ℤ → ℚ) := by
    intro X; ext i j; simp
  have hdet : ((M.det : ℤ) : ℚ) = (N : ℚ) ^ 2 * A.det := by
    have := (Int.castRingHom ℚ).map_det M
    rw [eq_intCast] at this
    rw [this, hcast, hM, det_smul]
    simp
  have hMdet : M.det ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hdet
    have := mul_eq_zero.mp hdet.symm
    rcases this with h1 | h1
    · exact hNq (pow_eq_zero_iff (by norm_num) |>.mp h1)
    · exact h h1
  obtain ⟨U, V, hU, hV, hUV⟩ := transpose_equiv M hMdet
  refine ⟨U, V, hU, hV, ?_⟩
  have hmap := congrArg (Int.castRingHom ℚ).mapMatrix hUV
  rw [map_mul, map_mul, hcast, hcast, hcast, hcast, Matrix.transpose_map, hM,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul] at hmap
  exact smul_right_injective _ hNq hmap

end TernaryPeriodPolynomials.RepresentationTheory.IntegerCartan
