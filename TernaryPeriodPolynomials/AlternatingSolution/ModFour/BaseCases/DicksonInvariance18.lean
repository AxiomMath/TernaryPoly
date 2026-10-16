module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs

@[expose] public section



/-!
# Invariance of the Dickson invariants under the eighteen `piSubstitutions`

Needed for Lemma 5.5 (`mf:lem:evenlift`) clause 4 (R₂-linearity): each of
`d4, d6, d7` (hence any polynomial in `d4, d6, d7`) is fixed by every one of
the eighteen substitutions used to define `piOperator`.
-/

open MvPolynomial
open TernaryPoly.CharTwoNorm (d4 d6 d7 invariant a b c cplus)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem my_ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly2) = ((n % 2 : ℕ) : Poly2) :=
  CharP.cast_eq_mod Poly2 2 n

theorem inv1 (i : Fin 3) :
    bind₁ (![X 1, X 2, X 0 + X 1] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv2 (i : Fin 3) :
    bind₁ (![X 2, X 1, X 0 + X 2] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv3 (i : Fin 3) :
    bind₁ (![X 0, X 2, X 0 + X 1] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv4 (i : Fin 3) :
    bind₁ (![X 0, X 2, X 1 + X 2] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv5 (i : Fin 3) :
    bind₁ (![X 0 + X 1, X 2, X 0] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv6 (i : Fin 3) :
    bind₁ (![X 0 + X 1, X 2, X 1] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv7 (i : Fin 3) :
    bind₁ (![X 2, X 0 + X 1 + X 2, X 0 + X 2] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv8 (i : Fin 3) :
    bind₁ (![X 0 + X 1 + X 2, X 2, X 1 + X 2] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv9 (i : Fin 3) :
    bind₁ (![X 0, X 1, X 0 + X 2] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv10 (i : Fin 3) :
    bind₁ (![X 0, X 1, X 1 + X 2] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv11 (i : Fin 3) :
    bind₁ (![X 1, X 0 + X 2, X 0] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv12 (i : Fin 3) :
    bind₁ (![X 1, X 0 + X 1 + X 2, X 0 + X 1] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv13 (i : Fin 3) :
    bind₁ (![X 0 + X 2, X 1, X 2] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv14 (i : Fin 3) :
    bind₁ (![X 0 + X 1 + X 2, X 1, X 1 + X 2] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv15 (i : Fin 3) :
    bind₁ (![X 0, X 1 + X 2, X 1] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv16 (i : Fin 3) :
    bind₁ (![X 0, X 0 + X 1 + X 2, X 0 + X 1] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv17 (i : Fin 3) :
    bind₁ (![X 0, X 1 + X 2, X 2] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

theorem inv18 (i : Fin 3) :
    bind₁ (![X 0, X 0 + X 1 + X 2, X 0 + X 2] : Fin 3 → Poly2) (invariant i) = invariant i := by
  fin_cases i <;> simp [invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [my_ofNat_mod] <;> norm_num

/-- Every one of the eighteen `piOperator` substitutions fixes `d4, d6, d7`. -/
theorem piSubstitutions_invariant :
    ∀ t ∈ piSubstitutions, ∀ i, bind₁ t (invariant i) = invariant i := by
  intro t ht
  simp only [piSubstitutions, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
  exacts [inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8, inv9,
          inv10, inv11, inv12, inv13, inv14, inv15, inv16, inv17, inv18]

/-- A polynomial built from `d4², d6², d7²` is fixed by every `piOperator` substitution. -/
theorem piSubstitutions_invariantSq_fixed {t : Fin 3 → Poly2} (ht : t ∈ piSubstitutions)
    (Q : MvPolynomial (Fin 3) (ZMod 2)) :
    bind₁ t (bind₁ ![d4 ^ 2, d6 ^ 2, d7 ^ 2] Q) = bind₁ ![d4 ^ 2, d6 ^ 2, d7 ^ 2] Q := by
  have h4 : bind₁ t d4 = d4 := by simpa [invariant] using piSubstitutions_invariant t ht 0
  have h6 : bind₁ t d6 = d6 := by simpa [invariant] using piSubstitutions_invariant t ht 1
  have h7 : bind₁ t d7 = d7 := by simpa [invariant] using piSubstitutions_invariant t ht 2
  rw [bind₁_bind₁]
  have hvec : (fun i => bind₁ t (![d4 ^ 2, d6 ^ 2, d7 ^ 2] i)) = ![d4 ^ 2, d6 ^ 2, d7 ^ 2] := by
    funext i
    fin_cases i <;> simp [map_pow, h4, h6, h7]
  rw [hvec]

end TernaryPeriodPolynomials.Argument.ModFourBeta
