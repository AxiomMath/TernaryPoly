module

public import TernaryPeriodPolynomials.SymmetricSolution.Residue.Fiber

@[expose] public section


/-!
# Equations of a rational hyperplane are proportional

Two linear forms on `ℚ³` with the same zero set are proportional (`same_kernel_proportional`).
Consequently every equation `L` of the rational hyperplane of `H` (a form vanishing exactly
where `denominator H` vanishes on `ℚ³`) is a nonzero multiple of `equation H`, and the
tensor-level residue of a fraction `p/L` agrees with the residue of `q/denominator H`
(`residue_independent_of_equation`).
-/

open MvPolynomial
open TernaryPoly.SinglePole
open scoped TensorProduct

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.ResidueTensor

/-- Evaluation of a linear form at a point is the dot product with its coefficients. -/
theorem eval_form (v x : Fin 3 → ℚ) : MvPolynomial.eval x (form v) = ∑ i, v i * x i := by
  simp [form]

/-- A monomial of degree one is a variable. -/
theorem monomial_degree_one (d : Fin 3 →₀ ℕ) (hd : d.degree = 1) :
    ∃ i, d = Finsupp.single i 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hd
  have h : (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 0) ∨ (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 0) ∨
      (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 1) := by omega
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact ⟨0, Finsupp.ext fun j => by fin_cases j <;> simp [h0, h1, h2]⟩
  · exact ⟨1, Finsupp.ext fun j => by fin_cases j <;> simp [h0, h1, h2]⟩
  · exact ⟨2, Finsupp.ext fun j => by fin_cases j <;> simp [h0, h1, h2]⟩

/-- Bridge: a degree-one element of `V_1` is the linear form of its coefficients. -/
theorem degree_one_eq_form (L : V 1) :
    L.val = form (fun i => L.val.coeff (Finsupp.single i 1)) := by
  ext d
  by_cases hd : d.degree = 1
  · obtain ⟨i, rfl⟩ := monomial_degree_one d hd
    rw [form_coeff]
  · exact (IsHomogeneous.coeff_eq_zero L.property hd).trans
      (IsHomogeneous.coeff_eq_zero (form_homogeneous (fun i => L.val.coeff (Finsupp.single i 1))) hd).symm

/-- The evaluation of `L ∈ V_1` on `ℚ³`, in coefficients. -/
theorem eval_equation (L : V 1) (x : Fin 3 → ℚ) :
    MvPolynomial.eval x L.val = ∑ i, L.val.coeff (Finsupp.single i 1) * x i := by
  have h := congrArg (MvPolynomial.eval x) (degree_one_eq_form L)
  rw [eval_form] at h
  exact h

/-- Two linear forms `a, b` on `ℚ³` (`a ≠ 0`) with the same zero set satisfy `b = c • a`, `c ≠ 0`. -/
theorem proportional_of_same_kernel (a b : Fin 3 → ℚ) (ha : a ≠ 0)
    (h : ∀ x : Fin 3 → ℚ, ∑ k, a k * x k = 0 ↔ ∑ k, b k * x k = 0) :
    ∃ c : ℚ, c ≠ 0 ∧ b = c • a := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hcon
    exact ha (funext fun i => by_contra fun hne => hcon ⟨i, hne⟩)
  have dot_single : ∀ (v : Fin 3 → ℚ) (j : Fin 3) (t : ℚ),
      ∑ k, v k * (Pi.single j t : Fin 3 → ℚ) k = v j * t := by
    intro v j t
    simp [Pi.single_apply, mul_ite]
  have dot_sub : ∀ (v x y : Fin 3 → ℚ),
      ∑ k, v k * (x - y) k = ∑ k, v k * x k - ∑ k, v k * y k := by
    intro v x y
    simp [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have key : ∀ j, b j * a i = b i * a j := by
    intro j
    have hx := (h (Pi.single j (a i) - Pi.single i (a j) : Fin 3 → ℚ)).mp (by
      rw [dot_sub, dot_single, dot_single]; ring)
    rw [dot_sub, dot_single, dot_single] at hx
    linear_combination hx
  refine ⟨b i / a i, ?_, ?_⟩
  · intro hc
    have hbi : b i = 0 := by
      rcases div_eq_zero_iff.mp hc with h0 | h0
      · exact h0
      · exact absurd h0 hi
    have hb : b = 0 := by
      funext j
      have hj := key j
      rw [hbi, zero_mul] at hj
      exact (mul_eq_zero.mp hj).resolve_right hi
    have h1 := (h (Pi.single i 1 : Fin 3 → ℚ)).mpr (by rw [hb]; simp)
    rw [dot_single] at h1
    exact hi (by simpa using h1)
  · funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hi]
    linear_combination key j

/-- Two linear forms on `ℚ³` with the same zero set are proportional. -/
theorem same_kernel_proportional (L M : V 1) (hM : M ≠ 0)
    (h : ∀ x : Fin 3 → ℚ, MvPolynomial.eval x L.val = 0 ↔ MvPolynomial.eval x M.val = 0) :
    ∃ c : ℚ, c ≠ 0 ∧ L = c • M := by
  have ha : (fun i => M.val.coeff (Finsupp.single i 1)) ≠ 0 := by
    intro h0
    apply hM
    apply Subtype.ext
    rw [degree_one_eq_form M]
    have h0' : (fun i => M.val.coeff (Finsupp.single i 1)) = fun _ => 0 := h0
    rw [h0']
    exact form_zero
  have hk : ∀ x : Fin 3 → ℚ, ∑ k, M.val.coeff (Finsupp.single k 1) * x k = 0 ↔
      ∑ k, L.val.coeff (Finsupp.single k 1) * x k = 0 := by
    intro x
    rw [← eval_equation M x, ← eval_equation L x]
    exact (h x).symm
  obtain ⟨c, hc, hb⟩ := proportional_of_same_kernel
    (fun i => M.val.coeff (Finsupp.single i 1)) (fun i => L.val.coeff (Finsupp.single i 1)) ha hk
  refine ⟨c, hc, Subtype.ext ?_⟩
  change L.val = c • M.val
  rw [degree_one_eq_form L, hb, form_smul, ← degree_one_eq_form M, MvPolynomial.smul_eq_C_mul]

/-- `L` is an equation of the rational hyperplane of `H`: on `ℚ³` it vanishes exactly where
`denominator H` does. -/
def IsEquationOf (H : Normal) (L : V 1) : Prop :=
  ∀ x : Fin 3 → ℚ, MvPolynomial.eval x L.val = 0 ↔ MvPolynomial.eval x (denominator H) = 0

/-- Every equation of `H` is a nonzero multiple of the chosen equation `equation H`. -/
theorem equation_proportional (H : Normal) (L : V 1) (hEq : IsEquationOf H L) :
    ∃ c : ℚ, c ≠ 0 ∧ L = c • equation H :=
  same_kernel_proportional L (equation H) (equation_ne_zero H) hEq

theorem span_eq_of_equation (H : Normal) (L : V 1) (hEq : IsEquationOf H L) :
    Submodule.span ℚ {L} = Submodule.span ℚ {equation H} := by
  obtain ⟨c, hc, rfl⟩ := equation_proportional H L hEq
  exact span_scale c hc (equation H)

theorem range_mulLin_eq (n : ℕ) (H : Normal) (L : V 1) (hEq : IsEquationOf H L) :
    LinearMap.range (mulLin n L) = LinearMap.range (mulLin n (equation H)) := by
  obtain ⟨c, hc, rfl⟩ := equation_proportional H L hEq
  exact range_mulLin_smul n hc (equation H)

/-- Residue independence: for an equation `L` of `H` and fractions with `p/L = q/denominator H`,
the tensor residues `[p] ⊗ L^∨` and `[q] ⊗ (denominator H)^∨` correspond under the canonical
identifications of the quotients and the duals (which depend only on the hyperplane). -/
theorem residue_independent_of_equation (n : ℕ) (H : Normal) (L : V 1) (hL : L ≠ 0)
    (hEq : IsEquationOf H L) (p q : V (n+1))
    (hfrac : embed p.val / embed L.val = embed q.val / embed (denominator H)) :
    TensorProduct.map (Submodule.quotEquivOfEq _ _ (range_mulLin_eq n H L hEq)).toLinearMap
      (LinearMap.dualMap (Submodule.inclusion (le_of_eq (span_eq_of_equation H L hEq).symm)))
      ((Submodule.Quotient.mk p : quotLin n L) ⊗ₜ[ℚ] lineDual L hL)
    = (Submodule.Quotient.mk q : quotLin n (equation H)) ⊗ₜ[ℚ]
        lineDual (equation H) (equation_ne_zero H) := by
  obtain ⟨c, hc, rfl⟩ := equation_proportional H L hEq
  have hD : denominator H ≠ 0 := denominator_ne_zero H
  have hval : (c • equation H).val = C c * denominator H := by
    show c • denominator H = C c * denominator H
    exact MvPolynomial.smul_eq_C_mul _ _
  have hne : embed (c • equation H).val ≠ 0 :=
    embed_ne_zero.mpr (fun h => hL (Subtype.ext h))
  have hne' : embed (denominator H) ≠ 0 := embed_ne_zero.mpr hD
  rw [div_eq_div_iff hne hne'] at hfrac
  have h1 : embed (p.val * denominator H) = embed (q.val * (c • equation H).val) := by
    rw [map_mul, map_mul]; exact hfrac
  have h2 := embed_injective h1
  rw [hval] at h2
  have h3 : p.val = C c * q.val := by
    apply mul_right_cancel₀ hD
    rw [h2]
    ring
  have hpq : p = c • q := Subtype.ext (by
    show p.val = c • q.val
    rw [MvPolynomial.smul_eq_C_mul]
    exact h3)
  subst hpq
  exact residue_scale_tensor n (equation H) (equation_ne_zero H) hc q

end TernaryPeriodPolynomials.Argument.Identities.ResidueTensor
