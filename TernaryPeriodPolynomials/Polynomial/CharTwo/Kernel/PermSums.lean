module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs

@[expose] public section





open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

/-- `Finset.univ` for `Equiv.Perm (Fin 3)` as an explicit list of the six permutations. -/
theorem univ_perm3 :
    (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {Equiv.refl (Fin 3), Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
       Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.swap 0 2 * Equiv.swap 0 1} := by
  decide

/-- Unfold a sum over all of `Equiv.Perm (Fin 3)` into six explicit terms. -/
theorem sum_univ_perm3 (f : Equiv.Perm (Fin 3) → Poly2) :
    ∑ σ : Equiv.Perm (Fin 3), f σ =
      f (Equiv.refl (Fin 3)) + f (Equiv.swap 0 1) + f (Equiv.swap 0 2) + f (Equiv.swap 1 2) +
      f (Equiv.swap 0 1 * Equiv.swap 0 2) + f (Equiv.swap 0 2 * Equiv.swap 0 1) := by
  rw [univ_perm3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem univ_zmod2 : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

/-- Unfold a sum over all of `ZMod 2` into two explicit terms. -/
theorem sum_univ_zmod2 (f : ZMod 2 → Poly2) : ∑ s : ZMod 2, f s = f 0 + f 1 := by
  rw [univ_zmod2, Finset.sum_insert (by decide), Finset.sum_singleton]

end TernaryPeriodPolynomials.Argument.CharTwoKernel
