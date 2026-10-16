module

public import TernaryPeriodPolynomials.Polynomial.CoefficientBaseChange
public import TernaryPeriodPolynomials.Polynomial.Definitions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section


/-!
# Corollary 1.4: the solution space splits into the symmetric and alternating sectors

Over a field `F` of characteristic zero, `solutionSpace F n = symmetricSolutionSpace F n ⊔
alternatingSolutionSpace F n` with trivial intersection, so
`dim W_n(F) = dim W_n^{sym}(F) + dim W_n^{alt}(F)`. The transposition `(x y)` preserves the
solution equations (it inverts the cyclic shift and commutes with the three-term norm), and its
two eigenspaces split the solution space because `2` is invertible.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument.Corollary14

section Swap

variable {R : Type*} [CommRing R]

local notation "V" => (Fin 3 → MvPolynomial (Fin 3) R)

/-- Composition of substitutions, with the composite substitution given by its components. -/
private theorem bind_comp (a b w : V) (f : MvPolynomial (Fin 3) R)
    (h : ∀ i, bind₁ a (b i) = w i) : bind₁ a (bind₁ b f) = bind₁ w f := by
  rw [bind₁_bind₁]
  have : (fun i => bind₁ a (b i)) = w := funext h
  rw [this]

/-- The transposition `(x y)` preserves the solution equations. -/
theorem solution_swap {f : MvPolynomial (Fin 3) R} (hf : Solution f) :
    Solution (bind₁ (![X 1, X 0, X 2] : V) f) := by
  obtain ⟨hc, hn⟩ := hf
  have hcc : bind₁ (![X 1, X 2, X 0] : V) (bind₁ (![X 1, X 2, X 0] : V) f) = f := by
    rw [hc, hc]
  refine And.intro ?_ ?_
  · -- cyclicity
    have e1 : bind₁ (![X 1, X 2, X 0] : V) (bind₁ (![X 1, X 0, X 2] : V) f) =
        bind₁ (![X 2, X 1, X 0] : V) f :=
      bind_comp (![X 1, X 2, X 0] : V) (![X 1, X 0, X 2] : V) (![X 2, X 1, X 0] : V) f (by
        intro i; fin_cases i <;> simp)
    have e2 : bind₁ (![X 1, X 0, X 2] : V) (bind₁ (![X 1, X 2, X 0] : V)
        (bind₁ (![X 1, X 2, X 0] : V) f)) = bind₁ (![X 0, X 2, X 1] : V)
          (bind₁ (![X 1, X 2, X 0] : V) f) :=
      bind_comp (![X 1, X 0, X 2] : V) (![X 1, X 2, X 0] : V) (![X 0, X 2, X 1] : V) _ (by
        intro i; fin_cases i <;> simp)
    have e3 : bind₁ (![X 0, X 2, X 1] : V) (bind₁ (![X 1, X 2, X 0] : V) f) =
        bind₁ (![X 2, X 1, X 0] : V) f :=
      bind_comp (![X 0, X 2, X 1] : V) (![X 1, X 2, X 0] : V) (![X 2, X 1, X 0] : V) f (by
        intro i; fin_cases i <;> simp)
    rw [e1, ← e3, ← e2, hcc]
  · -- the three-term norm
    have h := congrArg (bind₁ (![X 1, X 0, X 2] : V)) hn
    have e1 : bind₁ (![X 1, X 0, X 2] : V) (bind₁ (![-X 1, X 0 - X 1, X 2] : V) f) =
        bind₁ (![-X 0, X 1 - X 0, X 2] : V) f :=
      bind_comp (![X 1, X 0, X 2] : V) (![-X 1, X 0 - X 1, X 2] : V) (![-X 0, X 1 - X 0, X 2] : V)
        f (by intro i; fin_cases i <;> simp)
    have e2 : bind₁ (![X 1, X 0, X 2] : V) (bind₁ (![X 1 - X 0, -X 0, X 2] : V) f) =
        bind₁ (![X 0 - X 1, -X 1, X 2] : V) f :=
      bind_comp (![X 1, X 0, X 2] : V) (![X 1 - X 0, -X 0, X 2] : V) (![X 0 - X 1, -X 1, X 2] : V)
        f (by intro i; fin_cases i <;> simp)
    have e3 : bind₁ (![-X 1, X 0 - X 1, X 2] : V) (bind₁ (![X 1, X 0, X 2] : V) f) =
        bind₁ (![X 0 - X 1, -X 1, X 2] : V) f :=
      bind_comp (![-X 1, X 0 - X 1, X 2] : V) (![X 1, X 0, X 2] : V) (![X 0 - X 1, -X 1, X 2] : V)
        f (by intro i; fin_cases i <;> simp)
    have e4 : bind₁ (![X 1 - X 0, -X 0, X 2] : V) (bind₁ (![X 1, X 0, X 2] : V) f) =
        bind₁ (![-X 0, X 1 - X 0, X 2] : V) f :=
      bind_comp (![X 1 - X 0, -X 0, X 2] : V) (![X 1, X 0, X 2] : V) (![-X 0, X 1 - X 0, X 2] : V)
        f (by intro i; fin_cases i <;> simp)
    rw [map_add, map_add, map_zero, e1, e2] at h
    rw [e3, e4]
    linear_combination h

theorem swap_swap (f : MvPolynomial (Fin 3) R) :
    bind₁ (![X 1, X 0, X 2] : V) (bind₁ (![X 1, X 0, X 2] : V) f) = f := by
  rw [bind_comp (![X 1, X 0, X 2] : V) (![X 1, X 0, X 2] : V) (X : V) f (by
    intro i; fin_cases i <;> simp), bind₁_X_left, AlgHom.id_apply]

theorem swap_isHomogeneous {n : ℕ} {f : MvPolynomial (Fin 3) R} (hf : f.IsHomogeneous n) :
    (bind₁ (![X 1, X 0, X 2] : V) f).IsHomogeneous n := by
  have h : (aeval (![X 1, X 0, X 2] : V) f).IsHomogeneous (1 * n) :=
    hf.aeval _ (fun i => by fin_cases i <;> simp [isHomogeneous_X])
  rw [one_mul] at h
  exact h

end Swap

variable (F : Type*) [Field F] [CharZero F]

theorem symm_sup_alt_eq (n : ℕ) :
    symmetricSolutionSpace F n ⊔ alternatingSolutionSpace F n = solutionSpace F n := by
  apply le_antisymm
  · exact sup_le inf_le_left inf_le_left
  · intro f hf
    obtain ⟨hh, hs⟩ := (mem_solutionSpace n f).mp hf
    have hσ : bind₁ (![X 1, X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) F) f ∈ solutionSpace F n :=
      (mem_solutionSpace n _).mpr ⟨swap_isHomogeneous hh, solution_swap hs⟩
    rw [Submodule.mem_sup]
    refine ⟨(2 : F)⁻¹ • (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) F) f), ?_,
      (2 : F)⁻¹ • (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) F) f), ?_, ?_⟩
    · refine ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ hf hσ), ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply, map_smul,
        map_add, swap_swap]
      module
    · refine ⟨Submodule.smul_mem _ _ (Submodule.sub_mem _ hf hσ), ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      simp only [LinearMap.add_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply, map_smul,
        map_sub, swap_swap]
      module
    · rw [← smul_add]
      have : f + bind₁ (![X 1, X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) F) f + (f -
        bind₁ (![X 1, X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) F) f) = (2 : F) • f := by
        rw [two_smul]; abel
      rw [this, smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

theorem symm_inf_alt_eq (n : ℕ) :
    symmetricSolutionSpace F n ⊓ alternatingSolutionSpace F n = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro f ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at h1 h2
  simp only [LinearMap.sub_apply, LinearMap.add_apply, AlgHom.toLinearMap_apply,
    LinearMap.id_apply] at h1 h2
  have h3 : (2 : F) • f = 0 := by
    rw [two_smul]
    linear_combination h2 - h1
  exact (smul_eq_zero.mp h3).resolve_left two_ne_zero

/-- The dimension of the solution space is the sum of those of the two sectors. -/
theorem finrank_solutionSpace_eq (n : ℕ) :
    Module.finrank F (solutionSpace F n) =
      Module.finrank F (symmetricSolutionSpace F n) +
        Module.finrank F (alternatingSolutionSpace F n) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (symmetricSolutionSpace F n)
    (alternatingSolutionSpace F n)
  rw [symm_sup_alt_eq, symm_inf_alt_eq, finrank_bot, add_zero] at h
  exact h

end TernaryPeriodPolynomials.Argument.Corollary14
