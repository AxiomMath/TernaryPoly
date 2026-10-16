module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Edge
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Std
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.T3Chain

@[expose] public section


/-!
# Lemma B.1, tree maps: the standard edge is the cell `T₀`

Formalized by Claude Sonnet 5.5.

The ordered tuple `T3t = (e₀, p₁, p₂)` of lines has the labels `1 < 3 < 9`, so its orientation sign is `+1` and
`tupleVec 3 T3t = [T₀]` is the generator `single T0g 1` of the oriented cell `T₀`.  Hence the class `F3 p0` of the standard
oriented edge in `Φ(RG₃)` is the class of `⟨T₀⟩` (`F3_p0_genT0`).
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open CategoryTheory Finsupp TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract TernaryPoly.RankTwoAugmentedFrames
  TernaryPeriodPolynomials.Argument.FareyTree

theorem lab_e0 : e0L.label = 1 := by
  show labelVec ![1, 0, 0] = 1
  decide

theorem lab_p1 : p1.label = 3 := by
  show labelVec ![0, 1, 0] = 3
  decide

theorem lab_p2 : p2.label = 9 := by
  show labelVec ![0, 0, 1] = 9
  decide

theorem sgnLab_T3t : sgnLab T3t = 1 := by
  have h0 : Finset.Iio (0 : Fin 3) = ∅ := by decide
  have h1 : Finset.Iio (1 : Fin 3) = {0} := by decide
  have h2 : Finset.Iio (2 : Fin 3) = {0, 1} := by decide
  have l0 : (T3t 0).label = 1 := lab_e0
  have l1 : (T3t 1).label = 3 := lab_p1
  have l2 : (T3t 2).label = 9 := lab_p2
  unfold sgnLab
  rw [Fin.prod_univ_three, h0, h1, h2]
  simp [lsgn, l0, l1, l2]

theorem tupleCell_T3t : tupleCell tupleOK_T3t = T0g := by
  apply Subtype.ext
  apply Cell.ext
  exact image_T3t

theorem tupleVec_T3t : tupleVec 3 T3t = Finsupp.single T0g 1 := by
  rw [tupleVec_of_ok tupleOK_T3t, sgnLab_T3t, tupleCell_T3t, one_smul]

theorem F3_p0_genT0 : F3 p0 = clsU 3 (Finsupp.single T0g 1) := by
  rw [F3_p0, Eg_e12, tupleVec_T3t]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
