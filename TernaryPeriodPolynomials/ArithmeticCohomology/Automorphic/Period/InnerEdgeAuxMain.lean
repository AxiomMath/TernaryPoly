module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Period.InnerEdgeAux
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InnerParabolic
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Dimension
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.Main

@[expose] public section


/-!
# The edge class of an inner bad-line class is a period class

For an inner bad-line class `a`, the bad-line Shapiro coordinate `cuspRes … .line false a` is the
local class `innerBadLineLocalEquiv a`; it lies in the radical kernel `badLineLocalRadicalKernel`
and `badLineEdge` of it is, by construction, Sol's parabolic class
`innerBadLineParabolicMap a ∈ binaryParabolicH1`.  Eichler–Shimura surjectivity onto the parabolic
classes (`levelPeriodMap_range_eq_parabolic_of_injective`, with the injectivity of
`LevelThreeInjective.Main`) makes every such class `(n + 1)` times a period class.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.Automorphic.Period.InnerEdgeAux

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.LevelThree.BadLineLocal
open TernaryPeriodPolynomials.LevelThree.BadLineFinal
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle (S)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodDimension
  (levelPeriodMap_range_eq_parabolic_of_injective)
open TernaryPeriodPolynomials.LevelThreeInjective.Main
  (levelPeriodMap_injective_badLine)

/-- **Eichler–Shimura for the bad-line Levi cohomology.**  Every class of Sol's parabolic subspace
`binaryParabolicH1 n` is `(n + 1)` times the period class of a cusp form of weight `n + 3` for
`Γ₁(3)`. -/
theorem exists_period_of_mem_binaryParabolicH1 (n : ℕ)
    (P : CrossedH1 (binaryArithmeticRepresentation n)) (hP : P ∈ binaryParabolicH1 n) :
    ∃ f : S (n + 1), P = ((n + 1 : ℕ) : ℂ) • levelPeriodMap (n + 1) 0 f := by
  have hrange := levelPeriodMap_range_eq_parabolic_of_injective (m := n + 1) (e := 0)
    (Nat.succ_pos n) (levelPeriodMap_injective_badLine n)
  have hmem : P ∈ LinearMap.range (levelPeriodMap (n + 1) 0) := by
    rw [hrange]
    exact mem_parabolicH1_of_mem_binaryParabolicH1 n P hP
  obtain ⟨f', hf'⟩ := hmem
  have hc : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.succ_ne_zero
  refine ⟨((n + 1 : ℕ) : ℂ)⁻¹ • f', ?_⟩
  rw [map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  exact hf'.symm

/-- **The classical side of the direct route.**  The bad-line coordinate of every inner bad-line
class lies in the radical kernel and its edge class is `(n + 1)` times the period class of a cusp
form of weight `n + 3`. -/
theorem innerEdgeRealized_aux (n : ℕ) (hn : 0 < n) :
    ∀ a ∈ innerBadLineClasses n,
      ∃ y : badLineLocalRadicalKernel n,
        (y.1 : CuspH2 n trivialCharacter .line false) = cuspRes n trivialCharacter .line false a ∧
          ∃ f : S (n + 1), badLineEdge n hn y = ((n + 1 : ℕ) : ℂ) • levelPeriodMap (n + 1) 0 f := by
  intro a ha
  have hmem : (innerBadLineLocalEquiv n ⟨a, ha⟩).val ∈ badLineLocalRadicalKernel n :=
    locallyInner_standardBadLine_radical_zero n (innerBadLineLocalEquiv n ⟨a, ha⟩).val
      (innerBadLineLocalEquiv n ⟨a, ha⟩).property
  have key : badLineEdge n hn ⟨(innerBadLineLocalEquiv n ⟨a, ha⟩).val, hmem⟩ =
      (innerBadLineParabolicMap n hn ⟨a, ha⟩).val := rfl
  obtain ⟨f, hf⟩ := exists_period_of_mem_binaryParabolicH1 n _
    (innerBadLineParabolicMap n hn ⟨a, ha⟩).property
  exact ⟨⟨(innerBadLineLocalEquiv n ⟨a, ha⟩).val, hmem⟩, rfl, f, key.trans hf⟩

end TernaryPeriodPolynomials.Automorphic.Period.InnerEdgeAux
