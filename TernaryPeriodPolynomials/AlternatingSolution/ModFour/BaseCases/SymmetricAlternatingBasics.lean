module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Basics

@[expose] public section



/-!
# Symmetric/alternating closure facts for Lemma 5.5 clause 1

Base `IsSymmetric`/`IsAlternating` facts for the integral generators `liftA, liftB, liftC,
liftCplus, liftD4, liftD6, liftD7, liftDelta` (`Basics.lean`), plus generic closure helpers
(powers, products of mixed symmetry type, finite sums, and `bind₁` into symmetric generators)
needed to build the explicit lifts of Lemma 5.5 clause 1 (existence of symmetric/alternating
integral lifts of `expandOdd r` with even three-term norm).
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem perm3_cases (σ : Equiv.Perm (Fin 3)) :
    σ = 1 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 0 2 ∨ σ = Equiv.swap 1 2 ∨
    σ = Equiv.swap 0 1 * Equiv.swap 1 2 ∨ σ = Equiv.swap 1 2 * Equiv.swap 0 1 := by
  revert σ; decide

theorem liftA_isSymmetric : (liftA : MvPolynomial (Fin 3) ℤ).IsSymmetric := by
  intro σ
  rcases perm3_cases σ with h | h | h | h | h | h <;> subst h <;>
    simp [liftA, map_add, rename_X, Equiv.swap_apply_def] <;> ring

theorem liftB_isSymmetric : (liftB : MvPolynomial (Fin 3) ℤ).IsSymmetric := by
  intro σ
  rcases perm3_cases σ with h | h | h | h | h | h <;> subst h <;>
    simp [liftB, map_add, map_mul, rename_X, Equiv.swap_apply_def] <;> ring

theorem liftC_isSymmetric : (liftC : MvPolynomial (Fin 3) ℤ).IsSymmetric := by
  intro σ
  rcases perm3_cases σ with h | h | h | h | h | h <;> subst h <;>
    simp [liftC, map_mul, rename_X, Equiv.swap_apply_def] <;> ring

theorem liftDelta_isAlternating : IsAlternating (liftDelta : MvPolynomial (Fin 3) ℤ) := by
  intro σ
  rcases perm3_cases σ with h | h | h | h | h | h <;> subst h <;>
    simp [liftDelta, map_mul, map_sub, rename_X, Equiv.swap_apply_def,
      Equiv.Perm.sign_one, Equiv.Perm.sign_swap', Units.val_one, Units.val_neg, one_smul] <;>
    ring

theorem isSymmetric_pow {φ : MvPolynomial (Fin 3) ℤ} (h : φ.IsSymmetric) :
    ∀ n : ℕ, (φ ^ n).IsSymmetric := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem liftCplus_isSymmetric : (liftCplus : MvPolynomial (Fin 3) ℤ).IsSymmetric := by
  unfold liftCplus
  apply IsSymmetric.add
  · exact liftA_isSymmetric.mul liftB_isSymmetric
  · exact liftC_isSymmetric

theorem liftD4_isSymmetric : (liftD4 : MvPolynomial (Fin 3) ℤ).IsSymmetric := by
  unfold liftD4
  apply IsSymmetric.add
  apply IsSymmetric.add
  · exact isSymmetric_pow liftA_isSymmetric 4
  · exact isSymmetric_pow liftB_isSymmetric 2
  · exact liftA_isSymmetric.mul liftC_isSymmetric

theorem liftD6_isSymmetric : (liftD6 : MvPolynomial (Fin 3) ℤ).IsSymmetric := by
  unfold liftD6
  apply IsSymmetric.add
  apply IsSymmetric.add
  apply IsSymmetric.add
  · exact (isSymmetric_pow liftA_isSymmetric 2).mul (isSymmetric_pow liftB_isSymmetric 2)
  · exact (isSymmetric_pow liftA_isSymmetric 3).mul liftC_isSymmetric
  · exact (liftA_isSymmetric.mul liftB_isSymmetric).mul liftC_isSymmetric
  · exact isSymmetric_pow liftC_isSymmetric 2

theorem liftD7_isSymmetric : (liftD7 : MvPolynomial (Fin 3) ℤ).IsSymmetric := by
  unfold liftD7
  apply IsSymmetric.mul
  · exact liftA_isSymmetric.mul liftC_isSymmetric
  · apply IsSymmetric.add
    · exact liftA_isSymmetric.mul liftB_isSymmetric
    · exact liftC_isSymmetric

/-- Symmetric times alternating is alternating. -/
theorem symmetric_mul_alternating {s f : MvPolynomial (Fin 3) ℤ} (hs : s.IsSymmetric)
    (hf : IsAlternating f) : IsAlternating (s * f) := by
  intro σ
  rw [map_mul, hs σ, hf σ, mul_smul_comm]

/-- Alternating times symmetric is alternating. -/
theorem alternating_mul_symmetric {f s : MvPolynomial (Fin 3) ℤ} (hf : IsAlternating f)
    (hs : s.IsSymmetric) : IsAlternating (f * s) := by
  intro σ
  rw [map_mul, hf σ, hs σ, smul_mul_assoc]

/-- Finite-sum closure of `IsSymmetric`. -/
theorem isSymmetric_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 3) ℤ)
    (hf : ∀ i ∈ s, (f i).IsSymmetric) : (∑ i ∈ s, f i).IsSymmetric := by
  intro σ
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i hi => hf i hi σ)

/-- Finite-sum closure of `IsAlternating`. -/
theorem isAlternating_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 3) ℤ)
    (hf : ∀ i ∈ s, IsAlternating (f i)) : IsAlternating (∑ i ∈ s, f i) := by
  intro σ
  rw [map_sum, Finset.sum_congr rfl (fun i hi => hf i hi σ), Finset.smul_sum]

/-- Substituting any polynomial into generators that are each individually symmetric gives a
symmetric result, regardless of the substituted polynomial's own symmetry. -/
theorem bind₁_isSymmetric_of_symmetric {D : Fin 3 → MvPolynomial (Fin 3) ℤ}
    (hD : ∀ i, (D i).IsSymmetric) (P : MvPolynomial (Fin 3) ℤ) :
    (bind₁ D P).IsSymmetric := by
  intro σ
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add]; rw [hp, hq]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.bind₁_X_right]; rw [hp, hD i σ]

theorem exists_intCast_eq (ρ : ZMod 2) : ∃ n : ℤ, (n : ZMod 2) = ρ := by
  have h : ρ = 0 ∨ ρ = 1 := by revert ρ; decide
  rcases h with h | h
  · exact ⟨0, by rw [h]; norm_num⟩
  · exact ⟨1, by rw [h]; norm_num⟩

/-- Every polynomial over `ZMod 2` has some integral lift (not necessarily symmetric or
canonical in any way). -/
theorem exists_lift (ρ : Poly2) : ∃ s : MvPolynomial (Fin 3) ℤ, reduceTwo s = ρ := by
  induction ρ using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨n, hn⟩ := exists_intCast_eq a
    refine ⟨C n, ?_⟩
    show reduceTwo (C n) = C a
    simp only [MvPolynomial.map_C]
    congr 1
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    exact ⟨p' + q', by rw [map_add, hp', hq']⟩
  | mul_X p i hp =>
    obtain ⟨p', hp'⟩ := hp
    exact ⟨p' * X i, by rw [map_mul, hp', MvPolynomial.map_X]⟩

end TernaryPeriodPolynomials.Argument.ModFourBeta
