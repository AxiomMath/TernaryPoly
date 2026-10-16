module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Face.Interface
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CoeffAtT0

@[expose] public section


/-!
# Lemma B.1: the `a = 0` component of the coefficient at the standard cell, for the `H₀`-summand

Formalized by Claude Sonnet 5.5.

`comp0_coeffVal_lof`: for `W = Res_{Γ(6)} 𝓡_n`, `v` in the `H₀`-fibre and a grade-three cell `C`, the `a = 0` component of
`coeffVal W (lof v) C` (the coefficient `ρ(g) lof v` with `g C = T₀`, `g ∈ Γ(6)`) is `fiberAction(g) v` if that `g` lies in
`P_H` (equivalently in `P_N = P_H ∩ Γ(6)`) and `0` otherwise.  Hence for a cellular cycle coming from `(R ⊗ V)_{P_N}`,
`lit₀ comp₀ coeffAtT0` is the coefficient at the `P_N`-orbit of `T₀`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence CategoryTheory
open TernaryPoly.OrdinaryResidueSupport (rowAction axis)
open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
open scoped Classical

theorem comp0_rho_lof_of_not_mem (n : ℕ) {g : IntegralGL} (hg : g ∉ PH) (v : ResidueFiber n (axis 0)) :
    component n (axis 0) (rho n g (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) v)) = 0 := by
  have hne : axis 0 ≠ rowAction g⁻¹ (axis 0) := by
    intro h
    apply hg
    have : g⁻¹ ∈ PH := h.symm
    simpa using PH.inv_mem this
  have := action_lof_component_zero n (-1) g (axis 0) (axis 0) v hne
  simpa using this

theorem comp0_rho_lof_of_mem (n : ℕ) {g : IntegralGL} (hg : g ∈ PH) (v : ResidueFiber n (axis 0)) :
    component n (axis 0) (rho n g (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) v)) =
      fiberAction n g v := by
  rw [rho_PH_lof n hg]
  simp

theorem comp0_coeffVal_lof (n : ℕ) (v : ResidueFiber n (axis 0)) (C : Graded 3) :
    component n (axis 0)
        (coeffVal (Rep.res principalSix.subtype (ResRep n)) (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) v) C) =
      if h : ∃ g : principalSix, (g : IntegralGL) ∈ PH ∧ g • C = T0g then fiberAction n (h.choose : IntegralGL) v
      else 0 := by
  by_cases hex : ∃ g : principalSix, g • C = T0g
  · obtain ⟨g, hg⟩ := hex
    rw [coeffVal_eq _ _ C g hg]
    by_cases hgP : (g : IntegralGL) ∈ PH
    · have hex' : ∃ g : principalSix, (g : IntegralGL) ∈ PH ∧ g • C = T0g := ⟨g, hgP, hg⟩
      rw [dite_eq_left hex']
      have hch : hex'.choose = g :=
        translate_unique _ _ C.1 (congrArg Subtype.val hex'.choose_spec.2) (congrArg Subtype.val hg)
      rw [hch]
      exact comp0_rho_lof_of_mem n hgP v
    · have hex' : ¬ ∃ g : principalSix, (g : IntegralGL) ∈ PH ∧ g • C = T0g := by
        rintro ⟨g', hg'P, hg'⟩
        exact hgP (by
          have := translate_unique g' g C.1 (congrArg Subtype.val hg') (congrArg Subtype.val hg)
          rw [← this]; exact hg'P)
      rw [dite_eq_right hex']
      exact comp0_rho_lof_of_not_mem n hgP v
  · have hex' : ¬ ∃ g : principalSix, (g : IntegralGL) ∈ PH ∧ g • C = T0g := by
      rintro ⟨g', -, hg'⟩
      exact hex ⟨g', hg'⟩
    rw [dite_eq_right hex', coeffVal_eq_zero _ _ C hex, map_zero]

/-- **The identity-apartment residue of a class represented by a cellular cycle, from the flat bridge**: if the cell
cycle `z` of `cellCoinv (Res_{Γ(6)} 𝓡_n)` represents `ι_* w`, then `FidL w = κ dT0 · lit₀ comp₀ (coeffAtT0 z)`. -/
theorem FidL_eq_of_bridge {κ : ℚ} (hB : FlatIntersectionBridge κ) (n : ℕ)
    (w : groupHomology (Rep.res PN.subtype (FibRep n)) 3)
    (z : (cellCoinv (Rep.res principalSix.subtype (ResRep n))).X 3)
    (hz : ((cellCoinv (Rep.res principalSix.subtype (ResRep n))).d 3 2).hom z = 0)
    (hzw : (cellGroupHomologyMap (Rep.res principalSix.subtype (ResRep n)) 3).hom
      (cellClass (Rep.res principalSix.subtype (ResRep n)) z hz) = iotaStar n w) :
    FidL n w = (κ * dT0) • literalFiberMap n 0 (component n (axis 0)
      ((coeffAtT0 (Rep.res principalSix.subtype (ResRep n))).hom z)) := by
  change literalFiberMap n 0 (component n (axis 0)
      ((OrdinaryTopBoundaryComparison.groupApartmentEvaluation
        (Rep.res principalSix.subtype (ResRep n))).hom (iotaStar n w))) = _
  rw [← hzw, evaluation_eq_coeffAtT0 hB]
  simp only [map_smul]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
