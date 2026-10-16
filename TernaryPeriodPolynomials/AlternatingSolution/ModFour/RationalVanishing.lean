module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.IntegerVanishing

@[expose] public section



/-! Part (b) of `alternating_odd_degree_solution_eq_zero`: the rational case, by clearing denominators and
reducing to Part (a) (the integer case, `vanishing_of_odd_alternating_norm_zero_int`). -/

open MvPolynomial TernaryPeriodPolynomials.Argument

namespace TernaryPeriodPolynomials.Argument.ModFourMain

/-- `threeTermNorm` is natural with respect to applying a ring homomorphism to coefficients. -/
lemma threeTermNorm_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : MvPolynomial (Fin 3) R) :
    threeTermNorm (MvPolynomial.map φ f) = MvPolynomial.map φ (threeTermNorm f) := by
  have h1 : (fun i => MvPolynomial.map φ
      ((![-X 1, X 0 - X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) R) i)) =
      (![-X 1, X 0 - X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) S) := by
    funext i; fin_cases i <;> simp
  have h2 : (fun i => MvPolynomial.map φ
      ((![X 1 - X 0, -X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) R) i)) =
      (![X 1 - X 0, -X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) S) := by
    funext i; fin_cases i <;> simp
  unfold threeTermNorm
  rw [map_add, map_add, MvPolynomial.map_bind₁, MvPolynomial.map_bind₁, h1, h2]

lemma isHomogeneous_of_map_isHomogeneous {φ : ℤ →+* ℚ} (hφ : Function.Injective φ)
    {f₀ : MvPolynomial (Fin 3) ℤ} {n : ℕ} (h : (MvPolynomial.map φ f₀).IsHomogeneous n) :
    f₀.IsHomogeneous n := by
  intro d hd
  apply h
  rw [MvPolynomial.coeff_map]
  intro hc
  exact hd (hφ (by rw [hc, map_zero]))

lemma isAlternating_of_map_isAlternating {φ : ℤ →+* ℚ}
    (hφ : Function.Injective
      (MvPolynomial.map φ : MvPolynomial (Fin 3) ℤ → MvPolynomial (Fin 3) ℚ))
    {f₀ : MvPolynomial (Fin 3) ℤ} (h : IsAlternating (MvPolynomial.map φ f₀)) :
    IsAlternating f₀ := by
  intro σ
  apply hφ
  rw [MvPolynomial.map_rename, map_zsmul]
  exact h σ

lemma threeTermNorm_eq_zero_of_map_eq_zero {φ : ℤ →+* ℚ}
    (hφ : Function.Injective
      (MvPolynomial.map φ : MvPolynomial (Fin 3) ℤ → MvPolynomial (Fin 3) ℚ))
    {f₀ : MvPolynomial (Fin 3) ℤ} (h : threeTermNorm (MvPolynomial.map φ f₀) = 0) :
    threeTermNorm f₀ = 0 := by
  apply hφ
  rw [← threeTermNorm_map, h, map_zero]

/-- Given `f : MvPolynomial (Fin 3) ℚ` and a common multiple `N` of the denominators of its
(finitely many) coefficients, `clearDenom f N` is the integer polynomial with
`map (Int.castRingHom ℚ) (clearDenom f N) = C (N:ℚ) * f` (see `clearDenom_spec`). -/
noncomputable def clearDenom (f : MvPolynomial (Fin 3) ℚ) (N : ℕ) : MvPolynomial (Fin 3) ℤ :=
  ∑ d ∈ f.support, MvPolynomial.monomial d (((N : ℚ) * f.coeff d).num)

lemma ratCast_den_mul_self (r : ℚ) : (r.den : ℚ) * r = (r.num : ℚ) := by
  have hden : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_pos.ne'
  have h := Rat.num_div_den r
  rw [eq_comm, eq_div_iff hden] at h
  rw [mul_comm]
  exact h

lemma isInt_mul_of_den_dvd (r : ℚ) (N : ℕ) (h : r.den ∣ N) :
    ∃ k : ℤ, (N : ℚ) * r = (k : ℚ) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨(k : ℤ) * r.num, ?_⟩
  have hN : (N : ℚ) * r = (k : ℚ) * ((r.den : ℚ) * r) := by
    rw [hk]; push_cast; ring
  rw [hN, ratCast_den_mul_self]
  push_cast
  ring

lemma clearDenom_spec (f : MvPolynomial (Fin 3) ℚ) (N : ℕ)
    (hN : ∀ d ∈ f.support, (f.coeff d).den ∣ N) :
    MvPolynomial.map (Int.castRingHom ℚ) (clearDenom f N) = C (N : ℚ) * f := by
  unfold clearDenom
  rw [map_sum]
  have hC : C (N : ℚ) * f = ∑ d ∈ f.support, MvPolynomial.monomial d ((N : ℚ) * f.coeff d) := by
    conv_lhs => rw [f.as_sum]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => MvPolynomial.C_mul_monomial)
  rw [hC]
  apply Finset.sum_congr rfl
  intro d hd
  rw [MvPolynomial.map_monomial]
  obtain ⟨k, hk⟩ := isInt_mul_of_den_dvd (f.coeff d) N (hN d hd)
  have hnum : ((N : ℚ) * f.coeff d).num = k := by rw [hk]; simp
  rw [hnum, hk]
  rfl

theorem vanishing_of_odd_alternating_norm_zero_rat {n : ℕ} (hn : Odd n)
    {f : MvPolynomial (Fin 3) ℚ} (hf : f.IsHomogeneous n) (halt : IsAlternating f)
    (hN : threeTermNorm f = 0) : f = 0 := by
  set N : ℕ := ∏ d ∈ f.support, (f.coeff d).den with hNdef
  have hNne : N ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun d _ => (f.coeff d).den_pos.ne')
  have hNdvd : ∀ d ∈ f.support, (f.coeff d).den ∣ N := fun d hd => Finset.dvd_prod_of_mem _ hd
  set φ : ℤ →+* ℚ := Int.castRingHom ℚ with hφdef
  set f₀ : MvPolynomial (Fin 3) ℤ := clearDenom f N with hf₀def
  have hspec : MvPolynomial.map φ f₀ = C (N : ℚ) * f := clearDenom_spec f N hNdvd
  have hφinj : Function.Injective φ := Int.cast_injective
  have hmapinj :
      Function.Injective (MvPolynomial.map φ : MvPolynomial (Fin 3) ℤ → MvPolynomial (Fin 3) ℚ) :=
    MvPolynomial.map_injective φ hφinj
  have hCNf_hom : (C (N : ℚ) * f).IsHomogeneous n := by
    intro d hd
    apply hf
    rw [MvPolynomial.coeff_C_mul] at hd
    intro hc
    exact hd (by rw [hc, mul_zero])
  have hCNf_alt : IsAlternating (C (N : ℚ) * f) := by
    intro σ
    have hs := halt σ
    rw [map_mul]
    have hrc : rename σ (C (N : ℚ) : MvPolynomial (Fin 3) ℚ) = C (N : ℚ) := by
      rw [← MvPolynomial.algebraMap_eq]
      exact AlgHom.commutes (rename σ) (N : ℚ)
    rw [hrc, hs, mul_smul_comm]
  have hCNf_norm : threeTermNorm (C (N : ℚ) * f) = 0 := by
    rw [threeTermNorm_C_mul, hN, mul_zero]
  have hf0_hom : f₀.IsHomogeneous n := by
    apply isHomogeneous_of_map_isHomogeneous hφinj
    rw [hspec]; exact hCNf_hom
  have hf0_alt : IsAlternating f₀ := by
    apply isAlternating_of_map_isAlternating hmapinj
    rw [hspec]; exact hCNf_alt
  have hf0_norm : threeTermNorm f₀ = 0 := by
    apply threeTermNorm_eq_zero_of_map_eq_zero hmapinj
    rw [hspec]; exact hCNf_norm
  have hf0_zero : f₀ = 0 := vanishing_of_odd_alternating_norm_zero_int hn hf0_hom hf0_alt hf0_norm
  have hCNf_zero : C (N : ℚ) * f = 0 := by rw [← hspec, hf0_zero, map_zero]
  have hCNne : (C (N : ℚ) : MvPolynomial (Fin 3) ℚ) ≠ 0 := by
    simp only [ne_eq, MvPolynomial.C_eq_zero]
    exact Nat.cast_ne_zero.mpr hNne
  exact (mul_eq_zero.mp hCNf_zero).resolve_left hCNne

end TernaryPeriodPolynomials.Argument.ModFourMain
