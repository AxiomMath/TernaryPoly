module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Basic

@[expose] public section


/-! Exact monomial coordinate bases for the finite low-degree certificates. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity
open MvPolynomial

def tripleExponent (a b c : ℕ) : Exponent :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single (⟨2, by decide⟩ : Fin 3) c

def coordinatePolynomial {ι : Type*} [Fintype ι] (e : ι → Exponent) (x : ι → ℝ) : Poly :=
  ∑ i, x i • monomial (e i) 1

theorem coordinatePolynomial_coeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Exponent) (he : Function.Injective e) (x : ι → ℝ) (i : ι) :
    (coordinatePolynomial e x).coeff (e i) = x i := by
  simp [coordinatePolynomial, coeff_monomial, he.eq_iff]

theorem coordinatePolynomial_reconstruct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Exponent) (he : Function.Injective e) {n : ℕ}
    (hc : ∀ d : Exponent, d.degree = n → ∃ i, e i = d)
    (p : Poly) (hp : p.IsHomogeneous n) :
    coordinatePolynomial e (fun i => p.coeff (e i)) = p := by
  ext d
  by_cases hd : ∃ i, e i = d
  · obtain ⟨i, rfl⟩ := hd
    exact coordinatePolynomial_coeff e he _ i
  · have hp0 : p.coeff d = 0 := by
      by_contra hp0
      exact hd (hc d (by simpa [Finsupp.degree_eq_weight_one, Pi.one_def] using hp hp0))
    have he0 : ∀ i, e i ≠ d := by simpa using hd
    simp [coordinatePolynomial, coeff_monomial, he0, hp0]

theorem coordinatePolynomial_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Exponent) (he : Function.Injective e) (x y : ι → ℝ) :
    factorialPairing (coordinatePolynomial e x) (coordinatePolynomial e y) =
      ∑ i, factorialWeight (e i) * x i * y i := by
  conv_lhs => lhs; unfold coordinatePolynomial
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    factorialPairing_monomial_one, coordinatePolynomial_coeff e he]
  apply Finset.sum_congr rfl
  intro i hi
  simp [mul_comm, mul_left_comm]


def lowExponent1 : Fin 3 → Exponent := ![tripleExponent 0 0 1, tripleExponent 0 1 0, tripleExponent 1 0 0]

theorem lowExponent1_injective : Function.Injective lowExponent1 := by
  intro i j h
  have h0 := congrArg (fun d : Exponent => d 0) h
  have h1 := congrArg (fun d : Exponent => d 1) h
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | (solve | norm_num [lowExponent1, tripleExponent, Finsupp.single_apply] at h0)
    | (solve | norm_num [lowExponent1, tripleExponent, Finsupp.single_apply] at h1)

theorem lowExponent1_complete (d : Exponent) (hd : d.degree = 1) : ∃ i, lowExponent1 i = d := by
  have hs : d 0 + d 1 + d 2 = 1 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_succ, add_assoc] using hd
  have ha : d 0 ≤ 1 := by omega
  have hb : d 1 ≤ 1 := by omega
  interval_cases ha0 : d 0 <;> interval_cases hb0 : d 1
  all_goals try omega
  all_goals first
    | (refine ⟨(⟨0, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent1, tripleExponent] <;> omega)
    | (refine ⟨(⟨1, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent1, tripleExponent] <;> omega)
    | (refine ⟨(⟨2, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent1, tripleExponent] <;> omega)

def lowExponent2 : Fin 6 → Exponent := ![tripleExponent 0 0 2, tripleExponent 0 1 1, tripleExponent 0 2 0, tripleExponent 1 0 1, tripleExponent 1 1 0, tripleExponent 2 0 0]

theorem lowExponent2_injective : Function.Injective lowExponent2 := by
  intro i j h
  have h0 := congrArg (fun d : Exponent => d 0) h
  have h1 := congrArg (fun d : Exponent => d 1) h
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | (solve | norm_num [lowExponent2, tripleExponent, Finsupp.single_apply] at h0)
    | (solve | norm_num [lowExponent2, tripleExponent, Finsupp.single_apply] at h1)

theorem lowExponent2_complete (d : Exponent) (hd : d.degree = 2) : ∃ i, lowExponent2 i = d := by
  have hs : d 0 + d 1 + d 2 = 2 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_succ, add_assoc] using hd
  have ha : d 0 ≤ 2 := by omega
  have hb : d 1 ≤ 2 := by omega
  interval_cases ha0 : d 0 <;> interval_cases hb0 : d 1
  all_goals try omega
  all_goals first
    | (refine ⟨(⟨0, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent2, tripleExponent] <;> omega)
    | (refine ⟨(⟨1, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent2, tripleExponent] <;> omega)
    | (refine ⟨(⟨2, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent2, tripleExponent] <;> omega)
    | (refine ⟨(⟨3, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent2, tripleExponent] <;> omega)
    | (refine ⟨(⟨4, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent2, tripleExponent] <;> omega)
    | (refine ⟨(⟨5, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent2, tripleExponent] <;> omega)

def lowExponent3 : Fin 10 → Exponent := ![tripleExponent 0 0 3, tripleExponent 0 1 2, tripleExponent 0 2 1, tripleExponent 0 3 0, tripleExponent 1 0 2, tripleExponent 1 1 1, tripleExponent 1 2 0, tripleExponent 2 0 1, tripleExponent 2 1 0, tripleExponent 3 0 0]

theorem lowExponent3_injective : Function.Injective lowExponent3 := by
  intro i j h
  have h0 := congrArg (fun d : Exponent => d 0) h
  have h1 := congrArg (fun d : Exponent => d 1) h
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | (solve | norm_num [lowExponent3, tripleExponent, Finsupp.single_apply] at h0)
    | (solve | norm_num [lowExponent3, tripleExponent, Finsupp.single_apply] at h1)

theorem lowExponent3_complete (d : Exponent) (hd : d.degree = 3) : ∃ i, lowExponent3 i = d := by
  have hs : d 0 + d 1 + d 2 = 3 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_succ, add_assoc] using hd
  have ha : d 0 ≤ 3 := by omega
  have hb : d 1 ≤ 3 := by omega
  interval_cases ha0 : d 0 <;> interval_cases hb0 : d 1
  all_goals try omega
  all_goals first
    | (refine ⟨(⟨0, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent3, tripleExponent] <;> omega)
    | (refine ⟨(⟨1, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent3, tripleExponent] <;> omega)
    | (refine ⟨(⟨2, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent3, tripleExponent] <;> omega)
    | (refine ⟨(⟨3, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent3, tripleExponent] <;> omega)
    | (refine ⟨(⟨4, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent3, tripleExponent] <;> omega)
    | (refine ⟨(⟨5, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent3, tripleExponent] <;> omega)
    | (refine ⟨(⟨6, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent3, tripleExponent] <;> omega)
    | (refine ⟨(⟨7, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent3, tripleExponent] <;> omega)
    | (refine ⟨(⟨8, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent3, tripleExponent] <;> omega)
    | (refine ⟨(⟨9, by decide⟩), ?_⟩; ext j; fin_cases j <;> simp [lowExponent3, tripleExponent] <;> omega)

end TernaryPoly.SL3PolynomialCoercivity
