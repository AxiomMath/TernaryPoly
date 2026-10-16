module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.UnitriangularConj

@[expose] public section


/-!
# A unipotent filtration of the homogeneous coefficient representation

Give the monomial `x₀^{e₀} x₁^{e₁} x₂^{e₂}` the weight `e₁ + 2 e₂`. An upper
unitriangular substitution `xᵢ ↦ xᵢ + Σ_{j > i} m_{ij} x_j` changes a polynomial only by
terms of strictly larger weight. Pulling this filtration back along `ρ(q⁻¹)` gives a finite
filtration `flagFiltration q` of `HomogeneousPoly n` on whose graded pieces every element
of `conjUnitri q` acts trivially.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open MvPolynomial GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness.Weight

/-- The weight `e₁ + 2 e₂` of an exponent vector. -/
def wt (e : Fin 3 →₀ ℕ) : ℕ := e 1 + 2 * e 2

theorem wt_add (e f : Fin 3 →₀ ℕ) : wt (e + f) = wt e + wt f := by
  simp only [wt, Finsupp.coe_add, Pi.add_apply]
  ring

/-- Polynomials all of whose monomials have weight at least `k`. -/
def Wsub (k : ℕ) : Submodule ℂ Poly := restrictSupport ℂ {e | k ≤ wt e}

theorem mem_Wsub {k : ℕ} {p : Poly} : p ∈ Wsub k ↔ ∀ e ∈ p.support, k ≤ wt e := by
  rw [Wsub, mem_restrictSupport_iff]
  exact ⟨fun h e he => h he, fun h e he => h e he⟩

theorem Wsub_anti {k l : ℕ} (h : k ≤ l) : Wsub l ≤ Wsub k := by
  intro p hp
  rw [mem_Wsub] at hp ⊢
  exact fun e he => h.trans (hp e he)

theorem mem_Wsub_zero (p : Poly) : p ∈ Wsub 0 := by
  rw [mem_Wsub]
  exact fun _ _ => Nat.zero_le _

theorem mul_mem_Wsub {a b : ℕ} {p s : Poly} (hp : p ∈ Wsub a) (hs : s ∈ Wsub b) :
    p * s ∈ Wsub (a + b) := by
  classical
  rw [mem_Wsub] at hp hs ⊢
  intro e he
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (support_mul p s he)
  rw [wt_add]
  exact Nat.add_le_add (hp x hx) (hs y hy)

theorem C_mul_mem_Wsub {k : ℕ} (c : ℂ) {p : Poly} (hp : p ∈ Wsub k) : C c * p ∈ Wsub k := by
  rw [C_mul']
  exact (Wsub k).smul_mem c hp

theorem X_mem_Wsub (i : Fin 3) : (X i : Poly) ∈ Wsub i.val := by
  classical
  rw [mem_Wsub]
  intro e he
  rw [support_X, Finset.mem_singleton] at he
  subst he
  fin_cases i <;> simp [wt]

/-- `p'` agrees with `p ∈ Wsub k` up to weight `k + 1`. -/
def Close (k : ℕ) (p p' : Poly) : Prop := p ∈ Wsub k ∧ p' - p ∈ Wsub (k + 1)

theorem close_congr {k k' : ℕ} (h : k = k') {p p' : Poly} (hc : Close k p p') : Close k' p p' :=
  h ▸ hc

theorem close_mul {a b : ℕ} {p p' s s' : Poly} (hp : Close a p p') (hs : Close b s s') :
    Close (a + b) (p * s) (p' * s') := by
  refine ⟨mul_mem_Wsub hp.1 hs.1, ?_⟩
  have hs' : s' ∈ Wsub b := by
    have := (Wsub b).add_mem (Wsub_anti (Nat.le_succ b) hs.2) hs.1
    simpa using this
  have e : p' * s' - p * s = (p' - p) * s' + p * (s' - s) := by ring
  rw [e]
  refine (Wsub (a + b + 1)).add_mem ?_ ?_
  · have := mul_mem_Wsub hp.2 hs'
    rwa [show a + 1 + b = a + b + 1 by omega] at this
  · have := mul_mem_Wsub hp.1 hs.2
    rwa [show a + (b + 1) = a + b + 1 by omega] at this

theorem close_one : Close 0 (1 : Poly) 1 := ⟨mem_Wsub_zero 1, by simp⟩

theorem close_C (c : ℂ) : Close 0 (C c : Poly) (C c) := ⟨mem_Wsub_zero _, by simp⟩

theorem close_pow {a : ℕ} {p p' : Poly} (hp : Close a p p') (m : ℕ) :
    Close (a * m) (p ^ m) (p' ^ m) := by
  induction m with
  | zero => simpa using close_one
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact close_congr (by ring) (close_mul ih hp)

/-- Upper unitriangular complex matrices. -/
def IsUnitriC (M : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  M 0 0 = 1 ∧ M 1 1 = 1 ∧ M 2 2 = 1 ∧ M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0

theorem close_X0 {M : Matrix (Fin 3) (Fin 3) ℂ} (hM : IsUnitriC M) :
    Close 0 (X 0) (linearForm M 0) := by
  obtain ⟨m00, m11, m22, m10, m20, m21⟩ := hM
  refine ⟨X_mem_Wsub 0, ?_⟩
  have e : linearForm M 0 - X 0 = C (M 0 1) * X 1 + C (M 0 2) * X 2 := by
    simp only [linearForm, Fin.sum_univ_three, m00, C_1, one_mul]
    ring
  rw [e]
  exact (Wsub 1).add_mem (C_mul_mem_Wsub _ (X_mem_Wsub 1))
    (C_mul_mem_Wsub _ (Wsub_anti (by norm_num) (X_mem_Wsub 2)))

theorem close_X1 {M : Matrix (Fin 3) (Fin 3) ℂ} (hM : IsUnitriC M) :
    Close 1 (X 1) (linearForm M 1) := by
  obtain ⟨m00, m11, m22, m10, m20, m21⟩ := hM
  refine ⟨X_mem_Wsub 1, ?_⟩
  have e : linearForm M 1 - X 1 = C (M 1 2) * X 2 := by
    simp only [linearForm, Fin.sum_univ_three, m10, m11, C_0, C_1, zero_mul, one_mul, zero_add]
    ring
  rw [e]
  exact C_mul_mem_Wsub _ (X_mem_Wsub 2)

theorem close_X2 {M : Matrix (Fin 3) (Fin 3) ℂ} (hM : IsUnitriC M) :
    Close 2 (X 2) (linearForm M 2) := by
  obtain ⟨m00, m11, m22, m10, m20, m21⟩ := hM
  refine ⟨X_mem_Wsub 2, ?_⟩
  have e : linearForm M 2 - X 2 = 0 := by
    simp only [linearForm, Fin.sum_univ_three, m20, m21, m22, C_0, C_1, zero_mul, one_mul,
      zero_add]
    ring
  rw [e]
  exact (Wsub _).zero_mem

theorem close_monomial {M : Matrix (Fin 3) (Fin 3) ℂ} (hM : IsUnitriC M) (e : Fin 3 →₀ ℕ) (c : ℂ) :
    Close (wt e) (monomial e c) (substitute M (monomial e c)) := by
  have hmono : (monomial e c : Poly) = C c * (X 0 ^ e 0 * X 1 ^ e 1 * X 2 ^ e 2) := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_three]
  have hsub : substitute M (monomial e c) =
      C c * (linearForm M 0 ^ e 0 * linearForm M 1 ^ e 1 * linearForm M 2 ^ e 2) := by
    rw [hmono]
    simp only [map_mul, map_pow, substitute_X]
    congr 1
    simp [substitute]
  rw [hsub, hmono]
  have h0 := close_pow (close_X0 hM) (e 0)
  have h1 := close_pow (close_X1 hM) (e 1)
  have h2 := close_pow (close_X2 hM) (e 2)
  refine close_congr ?_ (close_mul (close_C c) (close_mul (close_mul h0 h1) h2))
  simp [wt]

/-- **Unitriangular substitutions raise the weight filtration.** -/
theorem substitute_sub_mem {M : Matrix (Fin 3) (Fin 3) ℂ} (hM : IsUnitriC M) {k : ℕ} {p : Poly}
    (hp : p ∈ Wsub k) : substitute M p - p ∈ Wsub (k + 1) := by
  classical
  have hp' := mem_Wsub.mp hp
  rw [p.as_sum, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ (fun e he => ?_)
  exact Wsub_anti (Nat.succ_le_succ (hp' e he)) (close_monomial hM e (p.coeff e)).2

theorem homogeneous_Wsub_eq_zero {n : ℕ} (f : HomogeneousPoly n) (hf : f.val ∈ Wsub (2 * n + 1)) :
    f = 0 := by
  have hhom : f.val.IsHomogeneous n := (mem_homogeneousSubmodule n f.val).mp f.property
  have hsupp : f.val.support = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro e he
    have hw := mem_Wsub.mp hf e he
    have hdeg : Finsupp.degree e = n := by
      by_contra hne
      exact (mem_support_iff.mp he) (hhom.coeff_eq_zero hne)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hdeg
    simp only [wt] at hw
    omega
  apply Subtype.ext
  rw [Submodule.coe_zero, ← support_eq_empty]
  exact hsupp

end TernaryPeriodPolynomials.FlagExactness.Weight
