module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.PeterssonDomain

@[expose] public section


/-!
# The coset decomposition `SL₂(ℤ) = ⊔ Γ⁰(p) βᵢ` and a fundamental domain of `Γ⁰(p)`

`Γ⁰(p) = {γ ∈ SL₂(ℤ) : p ∣ γ₀₁}` (`upperLevel`). The `p + 1` elements `βᵢ` (`S` and `Tʲ`,
`0 ≤ j < p`) satisfy: for every `x ∈ SL₂(ℤ)` exactly one `βᵢ x` lies in `Γ⁰(p)` (`exists_beta_mul_mem`,
`beta_unique`). Hence the union of the translates `βᵢ • 𝒟` is a fundamental domain of the image of
`Γ⁰(p)` in `PGL(2,ℝ)` (`upperDomain_isFundamentalDomain`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane Matrix MeasureTheory
open scoped MatrixGroups Pointwise

namespace TernaryPeriodPolynomials.Spectral.PeterssonCosets

open PeterssonDomain

variable (p : Nat.Primes)

theorem SL_inv_01 (γ : SL(2, ℤ)) : (γ⁻¹ : SL(2, ℤ)) 0 1 = -γ 0 1 := by
  simp [adjugate_fin_two]

/-- `Γ⁰(p)`. -/
def upperLevel : Subgroup SL(2, ℤ) where
  carrier := {γ | (p.val : ℤ) ∣ γ 0 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change (p.val : ℤ) ∣ (a * b) 0 1
    have h : (a * b) 0 1 = a 0 0 * b 0 1 + a 0 1 * b 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [h]
    exact dvd_add (dvd_mul_of_dvd_right hb _) (dvd_mul_of_dvd_left ha _)
  inv_mem' {a} ha := by
    change (p.val : ℤ) ∣ (a⁻¹ : SL(2, ℤ)) 0 1
    rw [SL_inv_01]
    exact (dvd_neg).mpr ha

theorem mem_upperLevel {γ : SL(2, ℤ)} : γ ∈ upperLevel p ↔ (p.val : ℤ) ∣ γ 0 1 := Iff.rfl

theorem neg_mem_upperLevel {γ : SL(2, ℤ)} (h : γ ∈ upperLevel p) : -γ ∈ upperLevel p := by
  rw [mem_upperLevel] at h ⊢
  simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  exact (dvd_neg).mpr h

/-- The coset representatives `S` and `Tʲ`. -/
def beta : Option (Fin p.val) → SL(2, ℤ)
  | none => ModularGroup.S
  | some j => ModularGroup.T ^ (j.val : ℤ)

theorem beta_none_mul_01 (x : SL(2, ℤ)) : (beta p none * x) 0 1 = -x 1 1 := by
  simp [beta, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]

theorem beta_some_mul_01 (j : Fin p.val) (x : SL(2, ℤ)) :
    (beta p (some j) * x) 0 1 = x 0 1 + (j.val : ℤ) * x 1 1 := by
  have h : ∀ n : ℤ, (ModularGroup.T ^ n * x) 0 1 = x 0 1 + n * x 1 1 := by
    intro n
    simp [ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
  exact h _

theorem det_eq (x : SL(2, ℤ)) : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 1 := by
  have h := x.property
  rw [Matrix.det_fin_two] at h
  exact h

theorem not_dvd_both (x : SL(2, ℤ)) (h1 : (p.val : ℤ) ∣ x 0 1) (h2 : (p.val : ℤ) ∣ x 1 1) : False := by
  have hdvd : (p.val : ℤ) ∣ 1 := by
    rw [← det_eq x]
    exact dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_left h1 _)
  have := Int.le_of_dvd one_pos hdvd
  have := p.property.two_le
  omega

/-- **Existence**: some `βᵢ x` lies in `Γ⁰(p)`. -/
theorem exists_beta_mul_mem (x : SL(2, ℤ)) : ∃ i, beta p i * x ∈ upperLevel p := by
  have : Fact p.val.Prime := ⟨p.property⟩
  by_cases h : (p.val : ℤ) ∣ x 1 1
  · exact ⟨none, by rw [mem_upperLevel, beta_none_mul_01]; exact (dvd_neg).mpr h⟩
  · have hne : ((x 1 1 : ℤ) : ZMod p.val) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    let j : ZMod p.val := -((x 0 1 : ℤ) : ZMod p.val) * ((x 1 1 : ℤ) : ZMod p.val)⁻¹
    refine ⟨some ⟨j.val, ZMod.val_lt j⟩, ?_⟩
    rw [mem_upperLevel, beta_some_mul_01, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]
    simp only [j]
    field_simp
    ring

/-- **Uniqueness** of the index. -/
theorem beta_unique (x : SL(2, ℤ)) (i j : Option (Fin p.val)) (hi : beta p i * x ∈ upperLevel p)
    (hj : beta p j * x ∈ upperLevel p) : i = j := by
  rw [mem_upperLevel] at hi hj
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      rw [beta_none_mul_01] at hi
      rw [beta_some_mul_01] at hj
      exfalso
      have h2 : (p.val : ℤ) ∣ x 1 1 := (dvd_neg).mp hi
      have h1 : (p.val : ℤ) ∣ x 0 1 := by
        have := dvd_sub hj (dvd_mul_of_dvd_right h2 (j.val : ℤ))
        simpa using this
      exact not_dvd_both p x h1 h2
  | some i =>
    cases j with
    | none =>
      rw [beta_none_mul_01] at hj
      rw [beta_some_mul_01] at hi
      exfalso
      have h2 : (p.val : ℤ) ∣ x 1 1 := (dvd_neg).mp hj
      have h1 : (p.val : ℤ) ∣ x 0 1 := by
        have := dvd_sub hi (dvd_mul_of_dvd_right h2 (i.val : ℤ))
        simpa using this
      exact not_dvd_both p x h1 h2
    | some j =>
      rw [beta_some_mul_01] at hi hj
      have hdiff : (p.val : ℤ) ∣ ((i.val : ℤ) - j.val) * x 1 1 := by
        have := dvd_sub hi hj
        rwa [show x 0 1 + (i.val : ℤ) * x 1 1 - (x 0 1 + (j.val : ℤ) * x 1 1) =
          ((i.val : ℤ) - j.val) * x 1 1 by ring] at this
      have hpr : Prime (p.val : ℤ) := Nat.prime_iff_prime_int.mp p.property
      rcases hpr.dvd_or_dvd hdiff with h | h
      · have hi' := i.isLt
        have hj' := j.isLt
        have hzero := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
        congr 1
        apply Fin.ext
        omega
      · exfalso
        have h1 : (p.val : ℤ) ∣ x 0 1 := by
          have := dvd_sub hi (dvd_mul_of_dvd_right h (i.val : ℤ))
          simpa using this
        exact not_dvd_both p x h1 h

/-- The image of `Γ⁰(p)` in `PGL(2,ℝ)`. -/
abbrev upperImage : Subgroup PGL(2, ℝ) := (upperLevel p).map psl

theorem upperImage_le : upperImage p ≤ modularImage := by
  rintro _ ⟨γ, -, rfl⟩
  exact ⟨γ, rfl⟩

/-- The fundamental domain `⋃ᵢ βᵢ • 𝒟` of `Γ⁰(p)`. -/
def upperDomain : Set ℍ := ⋃ i, psl (beta p i) • ModularGroup.fd

/-- **`⋃ᵢ βᵢ 𝒟` is a fundamental domain of `Γ⁰(p)`.** -/
theorem upperDomain_isFundamentalDomain :
    IsFundamentalDomain (upperImage p) (upperDomain p) volume := by
  apply isFundamentalDomain_subgroup fd_isFundamentalDomain (upperImage_le p)
    (fun i => psl (beta p i)) (fun i => ⟨beta p i, rfl⟩)
  · rintro _ ⟨γ, rfl⟩
    obtain ⟨i, hi⟩ := exists_beta_mul_mem p γ
    refine ⟨i, psl (beta p i * γ), ⟨_, hi, rfl⟩, ?_⟩
    rw [map_mul, inv_mul_cancel_left]
  · rintro i j _ _ ⟨η, hη, rfl⟩ ⟨η', hη', rfl⟩ heq
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, psl_eq_iff] at heq
    rcases heq with heq | heq
    · have hi : beta p i * ((beta p i)⁻¹ * η) ∈ upperLevel p := by
        rw [mul_inv_cancel_left]; exact hη
      have hj : beta p j * ((beta p i)⁻¹ * η) ∈ upperLevel p := by
        rw [heq, mul_inv_cancel_left]; exact hη'
      have hij := beta_unique p _ i j hi hj
      subst hij
      have : η = η' := mul_left_cancel heq
      rw [this]
    · have hi : beta p i * ((beta p i)⁻¹ * η) ∈ upperLevel p := by
        rw [mul_inv_cancel_left]; exact hη
      have hj : beta p j * ((beta p i)⁻¹ * η) ∈ upperLevel p := by
        rw [heq, mul_neg, mul_inv_cancel_left]; exact neg_mem_upperLevel p hη'
      have hij := beta_unique p _ i j hi hj
      subst hij
      have : η = -η' := by
        have := heq
        rw [← mul_neg] at this
        exact mul_left_cancel this
      rw [this, psl_neg]

end TernaryPeriodPolynomials.Spectral.PeterssonCosets
