module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.Polynomial.CoefficientBaseChange

@[expose] public section



/-! Part (c) support: `IsAlternating` is equivalent to invariance under the 3-cycle
`(0 1 2)` together with anti-invariance under the single transposition `(0 1)` — exactly
the two conditions baked into `TernaryPoly.Paper.alternatingSolutionSpace`. This lets
`alternatingSolutionSpace`'s base-change equivalence
(`TernaryPoly.Paper.alternatingSolution_baseChangeEquiv`) be reused for the general
char-0 field case instead of redoing the finite-dimensional-ℚ-subspace argument by hand. -/

open MvPolynomial TernaryPeriodPolynomials.Argument TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument.ModFourMain

noncomputable def s01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
noncomputable def cyc : Equiv.Perm (Fin 3) := s01 * Equiv.swap 1 2

lemma sign_s01 : Equiv.Perm.sign s01 = -1 := by
  unfold s01; exact Equiv.Perm.sign_swap (by decide)

lemma sign_cyc : Equiv.Perm.sign cyc = 1 := by
  unfold cyc s01; decide

lemma perm_cases (σ : Equiv.Perm (Fin 3)) :
    σ = 1 ∨ σ = s01 ∨ σ = s01 * cyc ∨ σ = cyc * s01 ∨ σ = cyc ∨ σ = cyc * cyc := by
  unfold cyc s01; revert σ; decide

lemma rename_perm_mul {R : Type*} [CommRing R] (σ τ : Equiv.Perm (Fin 3))
    (f : MvPolynomial (Fin 3) R) :
    rename (⇑σ) (rename (⇑τ) f) = rename (⇑(σ * τ)) f := by
  rw [rename_rename]; congr 1

lemma rename_cyc_eq_bind1 {R : Type*} [CommRing R] (f : MvPolynomial (Fin 3) R) :
    rename (⇑cyc) f = bind₁ (![X 1, X 2, X 0] : Fin 3 → MvPolynomial (Fin 3) R) f := by
  have : (rename (⇑cyc) : MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R) =
      bind₁ (![X 1, X 2, X 0] : Fin 3 → MvPolynomial (Fin 3) R) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.rename_X, MvPolynomial.bind₁_X_right]
    fin_cases i <;> rfl
  rw [this]

lemma rename_s01_eq_bind1 {R : Type*} [CommRing R] (f : MvPolynomial (Fin 3) R) :
    rename (⇑s01) f = bind₁ (![X 1, X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) R) f := by
  have : (rename (⇑s01) : MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R) =
      bind₁ (![X 1, X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) R) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.rename_X, MvPolynomial.bind₁_X_right]
    fin_cases i <;> rfl
  rw [this]

/-- `IsAlternating` is equivalent to invariance under the 3-cycle `(0 1 2)` together with
anti-invariance under the transposition `(0 1)`. -/
lemma isAlternating_iff {R : Type*} [CommRing R] (f : MvPolynomial (Fin 3) R) :
    IsAlternating f ↔
      (bind₁ (![X 1, X 2, X 0] : Fin 3 → MvPolynomial (Fin 3) R) f = f ∧
        bind₁ (![X 1, X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) R) f = -f) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← rename_cyc_eq_bind1]
      have hh := h cyc
      simpa [sign_cyc] using hh
    · rw [← rename_s01_eq_bind1]
      have hh := h s01
      simpa [sign_s01] using hh
  · rintro ⟨hc, hs⟩
    have hc' : rename (⇑cyc) f = f := by rw [rename_cyc_eq_bind1]; exact hc
    have hs' : rename (⇑s01) f = -f := by rw [rename_s01_eq_bind1]; exact hs
    intro σ
    rcases perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · rw [hs', sign_s01]; simp
    · rw [← rename_perm_mul, hc', hs', map_mul, sign_s01, sign_cyc]; simp
    · rw [← rename_perm_mul, hs', map_neg, hc', map_mul, sign_cyc, sign_s01]; simp
    · rw [hc', sign_cyc]; simp
    · rw [← rename_perm_mul, hc', hc', map_mul, sign_cyc]; simp

/-- Membership in `TernaryPoly.Paper.alternatingSolutionSpace` unfolds to exactly the
project's own `IsHomogeneous ∧ IsAlternating ∧ threeTermNorm = 0`. -/
lemma mem_alternatingSolutionSpace_iff {R : Type*} [CommRing R] (f : MvPolynomial (Fin 3) R)
    (n : ℕ) :
    f ∈ alternatingSolutionSpace R n ↔
      f.IsHomogeneous n ∧ IsAlternating f ∧ threeTermNorm f = 0 := by
  rw [isAlternating_iff]
  unfold alternatingSolutionSpace solutionSpace threeTermNorm
  simp only [Submodule.mem_inf, mem_homogeneousSubmodule, mem_solutions, Solution,
    LinearMap.mem_ker, LinearMap.add_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply,
    add_eq_zero_iff_eq_neg]
  tauto

end TernaryPeriodPolynomials.Argument.ModFourMain
