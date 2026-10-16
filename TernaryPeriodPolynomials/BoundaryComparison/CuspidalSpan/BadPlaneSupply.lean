module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.BadPlaneSupplyPiece
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.EichlerInputOfPiece
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.PieceToForm
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.SumIdentity
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.LowWeightSupply
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Classical

@[expose] public section


/-!
# The level-one cuspidal supply at the bad plane

Lemma C.3 at the bad plane (`ar:lem:seed`, level one): the period class of every level-one cusp
form of weight `n + 3` is the bad-plane edge of an element of the automorphic plane span vanishing
at the good plane. This discharges hypothesis `h` of
`CuspidalSupply.parabolicPeriodRealized_of_cuspFormRealized`.

* `arithmeticPeriodCocycle_class_eq_per`: the arithmetic period class of an Eichler input is the
  level-one period class `per` of its classical form (`PeriodClassical`).
* `piece_realized`: a Reynolds-averaged piece of `sumIdentity` is realized (`eichlerInput_realized`
  through `eichlerInputOfPiece` and `EichlerInput.exists_classicalForm`; a zero average is
  realized by `0`).
* `cuspFormRealized`: sum over the pieces of `sumIdentity` (weight `≥ 6`); weight `4` is
  `cuspidalSupply_weightFour`.
-/


open UpperHalfPlane
open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke
open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.Spectral.LevelOneEichlerShimura
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EvenLevelThree
open TernaryPeriodPolynomials.Oldform (exists_cuspForm_cast)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

/-- Two parity-projected classical cocycles agree when the forms have the same function (the
weights, degrees and parities being equal). -/
theorem classicalArithmeticCocycle_congr {w w' : ℤ} (hw : w = w')
    (form : CuspForm levelOne w) (form' : CuspForm levelOne w')
    (hfun : (form : ℍ → ℂ) = form') (degree : ℕ) (weight_eq : w = (degree : ℤ) + 2)
    (weight_eq' : w' = (degree : ℤ) + 2) (even : Even degree) (twist : ℤ) {parity parity' : ℕ}
    (hp : parity = parity') (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (sign' : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity') :
    classicalArithmeticCocycle form degree weight_eq even twist parity sign =
      classicalArithmeticCocycle form' degree weight_eq' even twist parity' sign' := by
  subst hw hp
  obtain rfl : form = form' := DFunLike.coe_injective hfun
  rfl

/-- **The arithmetic period class of an Eichler input is the level-one period class of its
classical form.** -/
theorem arithmeticPeriodCocycle_class_eq_per {k : ℕ} {σ : CuspidalRepresentation}
    (I : EichlerInput σ (2 * k + 1)) (stages : AnalyticScalar.ContinuousStages σ)
    (f : CuspForm levelOne (-2 * hw (k + 1)))
    (hf : (f : ℍ → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector) :
    groupCohomology.H1π (arithmeticBinaryRep (2 * k + 1 + 1) (-1))
        (I.arithmeticPeriodCocycle stages) = per (k + 1) (-1) f := by
  have hI := I.weight
  have hhw : -2 * hw (k + 1) = -2 * I.halfWeight := by
    unfold hw
    push_cast at hI ⊢
    omega
  obtain ⟨form, hform⟩ := exists_cuspForm_cast hhw f
  have weight_eq : -2 * I.halfWeight = ((2 * k + 1 + 1 : ℕ) : ℤ) + 2 := by
    push_cast at hI ⊢
    omega
  have even : Even (2 * k + 1 + 1) := ⟨k + 1, by ring⟩
  have hpar : (1 : Fin 2).val = (parityOf (-1)).val := by
    have hodd : ¬ Even (-1 : ℤ) := by
      rw [Int.not_even_iff_odd]
      exact ⟨-1, by norm_num⟩
    simp only [parityOf, ite_eq_right hodd]
  have hcoc := classicalArithmeticCocycle_congr hhw.symm form f hform (2 * k + 1 + 1) weight_eq
    (weight_eq_r (k + 1)) even (-1) hpar periodSign_eq (parityOf_sign (-1))
  rw [I.arithmeticPeriodCocycle_eq_classical stages (form := form) (hform.trans hf) weight_eq even,
    hcoc]
  rfl

/-- **One piece of `sumIdentity` is realized**: its classical form is a level-one cusp form whose
period class is the bad-plane edge of an element of the automorphic plane span vanishing at the
good plane. -/
theorem piece_realized {k : ℕ} (hn : 0 < 2 * k + 1) (hodd : Odd (2 * k + 1))
    (M : CohomologicalCuspData (2 * k + 1))
    (v : levelThreeClassicalVectorsWt M.cusp (-(((2 * k + 1 : ℕ) : ℤ) + 3))) :
    ∃ g : CuspForm levelOne (-2 * hw (k + 1)),
      (g : ℍ → ℂ) = cuspScalarWeightedLinearWt M.cusp (-(((2 * k + 1 : ℕ) : ℤ) + 3)) 1
          (reynoldsAverage M.cusp v.1) ∧
      ∃ b ∈ automorphicPlaneSpan (2 * k + 1),
        cuspRes (2 * k + 1) trivialCharacter .plane true b = 0 ∧
        edgeH2 (2 * k + 1) hn hodd (cuspRes (2 * k + 1) trivialCharacter .plane false b) =
          per (k + 1) (-1) g := by
  by_cases hne : reynoldsAverage M.cusp v.1 = 0
  · refine ⟨0, ?_, 0, Submodule.zero_mem _, map_zero _, ?_⟩
    · rw [hne, map_zero]
      rfl
    · rw [map_zero, map_zero]
      exact map_zero _
  · let I : EichlerInput M.cusp (2 * k + 1) := eichlerInputOfPiece (m := k) rfl M v hne
    obtain ⟨form, hform⟩ :=
      TernaryPeriodPolynomials.Argument.CuspidalSpan.EichlerInput.exists_classicalForm I
        M.cohomological
    have hI := I.weight
    have hhw : -2 * I.halfWeight = -2 * hw (k + 1) := by
      unfold hw
      push_cast at hI ⊢
      omega
    obtain ⟨g, hg⟩ := exists_cuspForm_cast hhw form
    obtain ⟨b, hb, hgood, hedge⟩ := eichlerInput_realized hn hodd M I
    refine ⟨g, ?_, -b, Submodule.neg_mem _ hb, by rw [map_neg, hgood, neg_zero], ?_⟩
    · have key := cuspScalarWeightedLinearWt_two_mul M.cusp I.halfWeight 1
        (reynoldsAverage M.cusp v.1)
      rw [hI] at key
      rw [hg, hform]
      exact key.symm
    · have hneg : edgeH2 (2 * k + 1) hn hodd
            (cuspRes (2 * k + 1) trivialCharacter .plane false (-b)) =
          -edgeH2 (2 * k + 1) hn hodd (cuspRes (2 * k + 1) trivialCharacter .plane false b) := by
        rw [map_neg]
        exact map_neg _ _
      rw [hneg, hedge, neg_neg]
      exact arithmeticPeriodCocycle_class_eq_per I _ g (hg.trans hform)

/-- **A list of pieces is realized**, by induction (as `GoodPlaneSpan.PlaneSupply.plane_key`). -/
theorem list_realized {k : ℕ} (hn : 0 < 2 * k + 1) (hodd : Odd (2 * k + 1))
    (l : List (Σ D : CohomologicalCuspData (2 * k + 1),
      levelThreeClassicalVectorsWt D.cusp (-(((2 * k + 1 : ℕ) : ℤ) + 3)))) :
    ∃ g : CuspForm levelOne (-2 * hw (k + 1)),
      (g : ℍ → ℂ) = (l.map fun p => cuspScalarWeightedLinearWt p.1.cusp
          (-(((2 * k + 1 : ℕ) : ℤ) + 3)) 1 (reynoldsAverage p.1.cusp p.2.1)).sum ∧
      ∃ b ∈ automorphicPlaneSpan (2 * k + 1),
        cuspRes (2 * k + 1) trivialCharacter .plane true b = 0 ∧
        edgeH2 (2 * k + 1) hn hodd (cuspRes (2 * k + 1) trivialCharacter .plane false b) =
          per (k + 1) (-1) g := by
  induction l with
  | nil =>
    refine ⟨0, by simp, 0, Submodule.zero_mem _, map_zero _, ?_⟩
    rw [map_zero, map_zero]
    exact map_zero _
  | cons p l ih =>
    obtain ⟨g, hg, b, hb, hbg, hbe⟩ := ih
    obtain ⟨g', hg', b', hb', hbg', hbe'⟩ := piece_realized hn hodd p.1 p.2
    refine ⟨g' + g, ?_, b' + b, Submodule.add_mem _ hb' hb,
      by rw [map_add, hbg, hbg', add_zero], ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      rw [← hg, ← hg']
      rfl
    · have hadd : edgeH2 (2 * k + 1) hn hodd
            (cuspRes (2 * k + 1) trivialCharacter .plane false (b' + b)) =
          edgeH2 (2 * k + 1) hn hodd (cuspRes (2 * k + 1) trivialCharacter .plane false b') +
            edgeH2 (2 * k + 1) hn hodd (cuspRes (2 * k + 1) trivialCharacter .plane false b) := by
        rw [map_add]
        exact map_add _ _ _
      rw [hadd, hbe, hbe', map_add]

/-- **The level-one cuspidal supply at the bad plane**: hypothesis `h` of
`parabolicPeriodRealized_of_cuspFormRealized`. -/
theorem cuspFormRealized (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    ∀ (k : ℕ) (hnk : n = 2 * k + 1), ∀ f : CuspForm levelOne (-2 * hw (k + 1)),
      ∃ b ∈ automorphicPlaneSpan n, cuspRes n trivialCharacter .plane true b = 0 ∧
        edgeH2 n hn hodd (cuspRes n trivialCharacter .plane false b) =
          (show 2 * (k + 1) = n + 1 by rw [hnk]; omega) ▸ per (k + 1) (-1) f := by
  intro k hnk f
  subst hnk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact cuspidalSupply_weightFour _ hn hodd rfl f
  · obtain ⟨l, hl, -⟩ := sumIdentity (2 * k + 1) k rfl hk f
    obtain ⟨g, hg, b, hb, hgood, hedge⟩ := list_realized hn hodd l
    have hgf : g = f := DFunLike.coe_injective (hg.trans hl.symm)
    subst hgf
    exact ⟨b, hb, hgood, hedge⟩

end TernaryPeriodPolynomials.Argument.CuspidalSpan
