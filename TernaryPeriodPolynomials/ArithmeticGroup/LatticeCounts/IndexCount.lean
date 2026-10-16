module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.SeedK0
public import Mathlib.Algebra.Polynomial.Monomial

@[expose] public section


/-!
# Index count: the columns of `A` form a basis of `Λ_{s,t}` (part 2)

`Λ_{s,t} = {(u,v) ∈ ℤ_p² : su + tv ∈ ℤ_p}`.  For `(k, A)` as in `SeedK0.K0Spec`, the columns of `A`
lie in `Λ_{s,t}` (`K0Spec`, third component), every `w ∈ Λ_{s,t}` is an integral combination of
the columns (`exists_comb_of_K0`), and the columns are linearly independent since `det A = p^r ≠ 0`
(`indep_of_K0`).

Formalized by Claude Haiku 5.5.
-/

open Matrix PadicInt
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.IndexCount

variable {p : ℕ} [Fact p.Prime]

theorem exists_comb_of_K0 {r : ℕ} {s t : ℚ_[p]} {k : Matrix (Fin 3) (Fin 3) ℤ_[p]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[p]} (hK : K0Spec r s t k A)
    (w : Fin 2 → ℤ_[p]) (hw : ‖s * (w 0 : ℚ_[p]) + t * (w 1 : ℚ_[p])‖ ≤ 1) :
    ∃ z : Fin 2 → ℤ_[p], ∀ i : Fin 2, ∑ j, A i j * z j = w i := by
  set x : ℚ_[p] := -(s * (w 0 : ℚ_[p]) + t * (w 1 : ℚ_[p])) with hx
  have hxn : ‖x‖ ≤ 1 := by rw [hx, norm_neg]; exact hw
  set c : ℤ_[p] := ⟨x, hxn⟩ with hcdef
  have hc : (c : ℚ_[p]) = x := rfl
  set u : Fin 3 → ℤ_[p] := ![c, w 0, w 1] with hu
  set z3 : Fin 3 → ℤ_[p] := Matrix.adjugate k *ᵥ u with hz3
  have hk : k *ᵥ z3 = u := by
    rw [hz3, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hK.1, one_smul, Matrix.one_mulVec]
  have hk_i : ∀ i, ∑ j, k i j * z3 j = u i := fun i => congrFun hk i
  have hq : ∀ i, ∑ j, (k i j : ℚ_[p]) * (z3 j : ℚ_[p]) = (u i : ℚ_[p]) := by
    intro i
    rw [← hk_i i]
    simp
  have hu0 : (u 0 : ℚ_[p]) = x := by simp [hu, hc]
  have hu1 : (u 1 : ℚ_[p]) = (w 0 : ℚ_[p]) := by simp [hu]
  have hu2 : (u 2 : ℚ_[p]) = (w 1 : ℚ_[p]) := by simp [hu]
  -- row 2 of `L k` applied to `Z` is `u₀ + s u₁ + t u₂ = 0`
  have hrow2zero : ∑ j : Fin 3, (Lst s t * toQ k) 2 j * (z3 j : ℚ_[p]) = 0 := by
    simp only [Fin.sum_univ_three, Lk_row2]
    have h0 := hq 0
    have h1 := hq 1
    have h2 := hq 2
    simp only [Fin.sum_univ_three] at h0 h1 h2
    linear_combination h0 + s * h1 + t * h2 + hu0 + s * hu1 + t * hu2 + hx
  have hrow2 : ∑ j : Fin 3, (Lst s t * toQ k) 2 j * (z3 j : ℚ_[p]) =
      ((p : ℚ_[p]) ^ r)⁻¹ * (z3 2 : ℚ_[p]) := by
    simp only [Fin.sum_univ_three, hK.2.2.2.2.1, hK.2.2.2.2.2.1, hK.2.2.2.2.2.2]
    ring
  have hz2 : (z3 2 : ℚ_[p]) = 0 := by
    have h := hrow2zero
    rw [hrow2] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (hp_ne p r))
  have hz2' : (z3 (Fin.last 2) : ℚ_[p]) = 0 := hz2
  -- rows 0 and 1 of `L k` are rows 1 and 2 of `k`, so they give `w₀` and `w₁`
  have hrow : ∀ i : Fin 2, ∑ j : Fin 3, (Lst s t * toQ k) (Fin.castSucc i) j * (z3 j : ℚ_[p]) =
      (w i : ℚ_[p]) := by
    intro i
    fin_cases i
    · show ∑ j : Fin 3, (Lst s t * toQ k) 0 j * (z3 j : ℚ_[p]) = (w 0 : ℚ_[p])
      simp only [Lk_row0]
      rw [hq 1, hu1]
    · show ∑ j : Fin 3, (Lst s t * toQ k) 1 j * (z3 j : ℚ_[p]) = (w 1 : ℚ_[p])
      simp only [Lk_row1]
      rw [hq 2, hu2]
  refine ⟨fun j => z3 (Fin.castSucc j), fun i => ?_⟩
  have hfin : ∑ j : Fin 2, (A i j : ℚ_[p]) * (z3 (Fin.castSucc j) : ℚ_[p]) = (w i : ℚ_[p]) := by
    have h1 := hrow i
    rw [Fin.sum_univ_castSucc] at h1
    simp only [hz2', mul_zero, add_zero, hK.2.2.2.1] at h1
    exact h1
  show ∑ j : Fin 2, A i j * z3 (Fin.castSucc j) = w i
  apply PadicInt.ext
  exact hfin

theorem indep_of_K0 {r : ℕ} {s t : ℚ_[p]} {k : Matrix (Fin 3) (Fin 3) ℤ_[p]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[p]} (hK : K0Spec r s t k A)
    (z : Fin 2 → ℤ_[p]) (hz : ∀ i : Fin 2, ∑ j, A i j * z j = 0) : z = 0 := by
  have hne : (p : ℤ_[p]) ^ r ≠ 0 := by
    intro h
    apply hp_ne p r
    have := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) h
    simpa using this
  have hdet : A.det ≠ 0 := by rw [hK.2.1]; exact hne
  have hAz : A *ᵥ z = 0 := funext fun i => hz i
  have h1 : A.det • z = 0 := by
    have e : (Matrix.adjugate A * A) *ᵥ z = A.det • z := by
      rw [Matrix.adjugate_mul]
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
    rw [← e, ← Matrix.mulVec_mulVec, hAz, Matrix.mulVec_zero]
  rcases smul_eq_zero.mp h1 with h | h
  · exact absurd h hdet
  · exact h

/-- The columns of `A` form a `ℤ_p`-basis of `Λ_{s,t}`: they lie in `Λ_{s,t}`, span it integrally, and
are linearly independent. -/
theorem columns_basis_of_K0 {r : ℕ} {s t : ℚ_[p]} {k : Matrix (Fin 3) (Fin 3) ℤ_[p]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[p]} (hK : K0Spec r s t k A) :
    (∀ j : Fin 2, ‖s * (A 0 j : ℚ_[p]) + t * (A 1 j : ℚ_[p])‖ ≤ 1) ∧
    (∀ w : Fin 2 → ℤ_[p], ‖s * (w 0 : ℚ_[p]) + t * (w 1 : ℚ_[p])‖ ≤ 1 →
      ∃ z : Fin 2 → ℤ_[p], ∀ i : Fin 2, ∑ j, A i j * z j = w i) ∧
    (∀ z : Fin 2 → ℤ_[p], (∀ i : Fin 2, ∑ j, A i j * z j = 0) → z = 0) :=
  ⟨hK.2.2.1, fun w hw => exists_comb_of_K0 hK w hw, fun z hz => indep_of_K0 hK z hz⟩

end TernaryPeriodPolynomials.Argument.LatticeCounts.IndexCount

end
