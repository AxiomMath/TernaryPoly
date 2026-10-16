module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Boundary.Zero

@[expose] public section


/-!
# `β_0 ∘ T_p = q_0 β_0`

Assembly of `LevelThreeBoundaryZero`: summing the coset contributions of `(T_p z)(L^p)`
(`ev01_hecke_lower_p`), and using `β_0(w(L^p)) = p β_0(w)`, we obtain

`betaZero_levelHecke : β_0 (T_p x) = q_0 · β_0 x`,
`q_0 = qZero m e p = p ^ (-e) · (p ^ (m + 1) + ε_p ^ m)`.

For `e = 0` and odd `m` this is `p^{m+1} + ε_p`, the Hecke eigenvalue `ε + p^{k-1}` of the
Eisenstein series of weight `k = m + 2` for `Γ₁(3)` supported at the cusp `0`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryZeroHecke

open Matrix MvPolynomial
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators ParabolicBounds FullBound
open LevelThreeCosets LevelThreeHeckeH1 LevelThreeBoundaryFunctional LevelThreeBoundaryHecke
open LevelThreeBoundaryCusp LevelThreeBoundaryZero
open GeneralEisenstein

section Eigenvalue

variable (m : ℕ) (e : ℤ) (p : Nat.Primes)

/-- **The Eisenstein scalar at the cusp `0`**:
`q_0 = p ^ (-e) · (p ^ (m + 1) + ε_p ^ m)`, `ε_p = ±1 ≡ p mod 3`. -/
def qZero : ℂ :=
  (p.val : ℂ) ^ (-e) * ((p.val : ℂ) ^ (m + 1) + (((signP p : ℤˣ) : ℤ) : ℂ) ^ m)

variable (hp3 : p.val ≠ 3)

/-- `(T_p z)(L^p)` evaluated at `(0, 1)`. -/
theorem ev01_hecke_lower_p (z : crossedCocycles (levelRep m e)) :
    eval ![0, 1] ((crossedHeckeCocycles (levelCosets p hp3) (rationalRho m e) (levelRep m e)
      (level_compat m e) levelEmbed_injective z).val (lower (p.val : ℤ))).val =
      (p.val : ℂ) ^ (-e) * ((p.val : ℂ) ^ (m + 2) + (p.val : ℂ) *
        (((signP p : ℤˣ) : ℤ) : ℂ) ^ m) * eval ![0, 1] (z.val (lower 1)).val := by
  have hsum : (crossedHeckeCocycles (levelCosets p hp3) (rationalRho m e) (levelRep m e)
      (level_compat m e) levelEmbed_injective z).val (lower (p.val : ℤ)) =
      ∑ j : Option (Fin p.val), rationalRho m e (heckeRep p j)⁻¹
        (z.val (levelDelta p hp3 (lower (p.val : ℤ)) j)) :=
    levelHeckeCocycles_apply m e p hp3 z (lower (p.val : ℤ))
  have hmap : eval ![0, 1] (∑ j : Option (Fin p.val), rationalRho m e (heckeRep p j)⁻¹
        (z.val (levelDelta p hp3 (lower (p.val : ℤ)) j)) : Binary.HomogeneousPoly m).val =
      ∑ j : Option (Fin p.val), eval ![0, 1] (rationalRho m e (heckeRep p j)⁻¹
        (z.val (levelDelta p hp3 (lower (p.val : ℤ)) j)) : Binary.HomogeneousPoly m).val := by
    exact map_sum (SymFixed.evalAt (m := m) ![0, 1]) _ _
  have hnone : eval ![0, 1] (rationalRho m e (heckeRep p none)⁻¹
      (z.val (levelDelta p hp3 (lower (p.val : ℤ)) none)) : Binary.HomogeneousPoly m).val =
      (p.val : ℂ) ^ (-e) * ((((signP p : ℤˣ) : ℤ) : ℂ) ^ m *
        eval ![0, 1] (z.val (lower 1)).val) := by
    rw [ev01_inv_none, levelDelta_lower_none, eval_lower_one_value]
  have hT : ∀ i : Fin p.val, eval ![0, 1] (rationalRho m e (heckeRep p (some i))⁻¹
      (z.val (levelDelta p hp3 (lower (p.val : ℤ)) (some i))) : Binary.HomogeneousPoly m).val =
      (p.val : ℂ) ^ (-e) * ((((signP p : ℤˣ) : ℤ) : ℂ) ^ m * eval ![0, 1] (z.val (lower 1)).val) +
      (if i.val = 0 then (p.val : ℂ) ^ (-e) * (((p.val : ℂ) ^ (m + 2) -
        (((signP p : ℤˣ) : ℤ) : ℂ) ^ m) * eval ![0, 1] (z.val (lower 1)).val) else 0) := by
    intro i
    by_cases hi : i.val = 0
    · have hi' : i = ⟨0, p.property.pos⟩ := Fin.ext hi
      subst hi'
      rw [ev01_inv_some, levelDelta_lower_zero, eval_lower_sq_value, ite_eq_left hi]
      push_cast
      ring1
    · rw [ev01_inv_some, levelDelta_lower_some, eval_hElt_value m e p hp3 z i hi, ite_eq_right hi,
        add_zero]
  have hsome : ∑ i : Fin p.val, eval ![0, 1] (rationalRho m e (heckeRep p (some i))⁻¹
      (z.val (levelDelta p hp3 (lower (p.val : ℤ)) (some i))) : Binary.HomogeneousPoly m).val =
      (p.val : ℂ) * ((p.val : ℂ) ^ (-e) * ((((signP p : ℤˣ) : ℤ) : ℂ) ^ m *
        eval ![0, 1] (z.val (lower 1)).val)) +
      (p.val : ℂ) ^ (-e) * (((p.val : ℂ) ^ (m + 2) - (((signP p : ℤˣ) : ℤ) : ℂ) ^ m) *
        eval ![0, 1] (z.val (lower 1)).val) := by
    rw [Finset.sum_congr rfl (fun i _ => hT i), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    rw [Finset.sum_eq_single (⟨0, p.property.pos⟩ : Fin p.val)]
    · simp
    · intro i _ hne
      have hi : i.val ≠ 0 := fun h => hne (Fin.ext h)
      rw [ite_eq_right hi]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum, hmap, Fintype.sum_option, hnone, hsome]
  ring1

/-- The cocycle-level formula: `β_0((T_p z)(L)) = q_0 β_0(z(L))`. -/
theorem ev01_hecke_lower (z : crossedCocycles (levelRep m e)) :
    eval ![0, 1] ((crossedHeckeCocycles (levelCosets p hp3) (rationalRho m e) (levelRep m e)
      (level_compat m e) levelEmbed_injective z).val (lower 1)).val =
      qZero m e p * eval ![0, 1] (z.val (lower 1)).val := by
  have h1 := ev01_hecke_lower_p m e p hp3 z
  have h2 := ev01_cocycle_pow m e (crossedHeckeCocycles (levelCosets p hp3) (rationalRho m e)
    (levelRep m e) (level_compat m e) levelEmbed_injective z) p.val
  rw [lower_pow_nat] at h2
  have hp0 : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  apply mul_left_cancel₀ hp0
  unfold qZero
  linear_combination h1 - h2

/-- **Hecke equivariance of the boundary functional at `0`**:
`β_0 (T_p x) = q_0 · β_0 x`. -/
theorem betaZero_levelHecke (x : CrossedH1 (levelRep m e)) :
    betaZero m e (levelHecke m e p hp3 x) = qZero m e p * betaZero m e x :=
  cuspFunctional_map (levelRep m e) (lower 1) (SymFixed.evalAt (m := m) ![0, 1])
    (evalZero_sub m e) (levelHecke m e p hp3)
    (fun z => crossedHeckeCocycles (levelCosets p hp3) (rationalRho m e) (levelRep m e)
      (level_compat m e) levelEmbed_injective z)
    (levelHecke_mk m e p hp3) (qZero m e p) (ev01_hecke_lower m e p hp3) x

end Eigenvalue

end TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryZeroHecke
