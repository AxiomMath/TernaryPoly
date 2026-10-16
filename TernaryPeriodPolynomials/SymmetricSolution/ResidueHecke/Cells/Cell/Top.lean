module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.TreeRes
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.ResolutionZ

@[expose] public section


/-!
# The oriented cell resolution has length three

Formalized by Claude Sonnet 5.5.

There are no cells of grade four (`Cell.grade_le`), so `d₄ = 0` in `RG_projRes H`, and the top differentials of the
coinvariant complexes `CxN N (YAR R A)`, `CxK (YAR R A)` vanish (the hypothesis of `cycleClass_injective_top`).
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPeriodPolynomials.FreeResolution TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.HochschildSerre
open TernaryPeriodPolynomials.Argument.GroupHomology

instance isEmpty_graded_four : IsEmpty (Graded 4) :=
  ⟨fun x => by
    have h1 := Cell.grade_le x.1
    have h2 := x.2
    omega⟩

theorem dRG_three : dRG 3 = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  have : z = 0 := Subsingleton.elim (α := Graded 4 →₀ ℚ) _ _
  rw [this, map_zero]
  rfl

theorem RG_projRes_d_four (H : Subgroup IntegralGL3) : (RG_projRes H).complex.d 4 3 = 0 := by
  change (RGH H).d 4 3 = 0
  rw [RGH_d H 3, dRG_three]
  exact Functor.map_zero _ _ _

theorem CxN_d_four {K : Type} [Group K] (N : Subgroup K) (A : Rep.{0} ℚ K)
    (R : ProjectiveResolution (Rep.trivial ℚ K ℚ)) (h : R.complex.d 4 3 = 0) :
    (CxN N (YAR R A)).d 4 3 = 0 := by
  change (cN N).map ((tensorLeft A).map (R.complex.d 4 3)) = 0
  rw [h]
  simp

theorem CxK_d_four {K : Type} [Group K] (A : Rep.{0} ℚ K)
    (R : ProjectiveResolution (Rep.trivial ℚ K ℚ)) (h : R.complex.d 4 3 = 0) :
    (CxK (YAR R A)).d 4 3 = 0 := by
  change (cK (K := K)).map ((tensorLeft A).map (R.complex.d 4 3)) = 0
  rw [h]
  simp

end TernaryPeriodPolynomials.Argument.AppendixBResidue
