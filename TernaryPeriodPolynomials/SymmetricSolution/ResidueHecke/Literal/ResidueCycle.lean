module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.LiteralKappa
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.HeckeResidue

@[expose] public section


/-!
# Lemma 4.5, sentence 1: the residue cycle `F_q` and `H₃(G, ℛ_n ⊗ det) ≅ ℬ_{n+1}`

Formalized by Claude Sonnet 5.5.
Paper: Lemma 4.5 (`lem:residue-period`) and its proof (the representative `F_q` in the paper).

For a period `q ∈ ℬ_{n+1}` the residue cycle of the lemma is the residue
`F_q = res (q(b,c)/a + q(a,c)/b + q(a,b)/c) ∈ ℛ_n`; its three coordinate components are the literal
numerators `q(b,c)`, `q(a,c)`, `q(a,b)` over the three coordinate hyperplanes and all other components vanish.

**Proved (literal group homology).**

* `Fq_coordinate`, `Fq_noncoordinate`: the components of `F_q`.
* `value_eq_Fq`: for every class `x ∈ H₃(GL₃(ℤ), ℛ_n ⊗ det⁻¹)` (Mathlib's `groupHomology`), the value of its Steinberg
  functional `H3_G_equiv n x` at the identity apartment is the residue cycle `F_{res_H x}` of its literal residue.
* `lemma_4_5_residue_cycle`: for every `q ∈ ℬ_{n+1}` there is a unique class `x` with literal residue `q`, and its value at the
  identity apartment is `F_q`.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma45Literal

open TernaryPoly TernaryPoly.SinglePole TernaryPoly.SinglePoleCoordinate TernaryPoly.SinglePoleSupport
  TernaryPoly.OrdinaryFullCoefficient TernaryPoly.OrdinaryResidueSupport
open TernaryPeriodPolynomials.Argument.AppendixBResidue

/-- **The residue cycle `F_q`**: the residue of the rational function
`q(b,c)/a + q(a,c)/b + q(a,b)/c`, an element of `ℛ_n`. -/
def Fq (n : ℕ) (q : OrdinaryResiduePeriod.periodSpace (n + 1)) : Residues n :=
  residue n (canonicalRepresentative n q.val)

/-- The rational function of which `F_q` is the residue, written out literally. -/
theorem canonicalRepresentative_literal_formula (n : ℕ) (q : OrdinaryResiduePeriod.periodSpace (n + 1)) :
    (canonicalRepresentative n q.val).val =
      embed (MvPolynomial.rename (![1, 2] : Fin 2 → Fin 3) (q.val : BinaryV (n + 1)).val) / embed (MvPolynomial.X 0) +
      embed (MvPolynomial.rename (![0, 2] : Fin 2 → Fin 3) (q.val : BinaryV (n + 1)).val) / embed (MvPolynomial.X 1) +
      embed (MvPolynomial.rename (![0, 1] : Fin 2 → Fin 3) (q.val : BinaryV (n + 1)).val) / embed (MvPolynomial.X 2) :=
  canonicalRepresentative_val n q.val

/-- `F_q = canonicalMap q`, the library's linear form of the same residue. -/
theorem Fq_eq_canonicalMap (n : ℕ) (q : OrdinaryResiduePeriod.periodSpace (n + 1)) :
    Fq n q = OrdinaryResiduePeriod.canonicalMap n q.val :=
  (OrdinaryResiduePeriod.canonicalMap_apply n q.val).symm

/-- Every coordinate hyperplane `a = 0`, `b = 0`, `c = 0` carries the literal numerator `q`
(i.e. `q(b,c)`, `q(a,c)`, `q(a,b)` in the respective variables). -/
theorem Fq_coordinate (n : ℕ) (q : OrdinaryResiduePeriod.periodSpace (n + 1)) (i : Fin 3) :
    coordinateTuple n (Fq n q) i = q.val :=
  OrdinaryResidueGeneral.canonical_coordinateResidue n q.val i

/-- The components of `F_q` along non-coordinate hyperplanes vanish. -/
theorem Fq_noncoordinate (n : ℕ) (q : OrdinaryResiduePeriod.periodSpace (n + 1)) (H : SinglePole.Normal)
    (hH : ¬ Coordinate H) : Fq n q H = 0 := by
  rw [Fq_eq_canonicalMap]
  unfold OrdinaryResiduePeriod.canonicalMap
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rw [DFinsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hne : axis i ≠ H := fun h => hH ⟨i, h.symm⟩
  exact DirectSum.of_eq_of_ne _ _ _ hne.symm

/-- The functional of a class `x ∈ H₃(G, ℛ_n ⊗ det⁻¹)` at the identity apartment *is* the residue cycle
`F_q` of its literal residue `q = res_H x`. -/
theorem value_eq_Fq (n : ℕ) (x : groupHomology (ResRep n) 3) :
    (H3_G_equiv n x).val (OrdinaryApartmentPresentation.frameCycle 1) = Fq n (resHLit n x) := by
  have h1 : (H3_G_equiv n x) = (OrdinaryResiduePeriod.periodEquiv n).symm (resHLit n x) := by
    apply (OrdinaryResiduePeriod.periodEquiv n).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    change _ = (resH n (H3_G_equiv n x)).val
    rw [resH_eq_periodEquiv]
  have h2 := OrdinaryResiduePeriod.periodEquiv_symm_reference n (resHLit n x)
  rw [h1]
  exact h2.trans (Fq_eq_canonicalMap n _).symm

/-- `x ↦ res_H x` as a linear equivalence `H₃(G, ℛ_n ⊗ det⁻¹) ≃ ℬ_{n+1}` (the duality followed by the period coordinate). -/
def resHLitEquiv (n : ℕ) : groupHomology (ResRep n) 3 ≃ₗ[ℚ] OrdinaryResiduePeriod.periodSpace (n + 1) :=
  (H3_G_equiv n).trans (OrdinaryResiduePeriod.periodEquiv n)

theorem resHLitEquiv_apply (n : ℕ) (x : groupHomology (ResRep n) 3) : resHLitEquiv n x = resHLit n x := by
  apply Subtype.ext
  change (OrdinaryResiduePeriod.periodEquiv n (H3_G_equiv n x)).val = (resH n (H3_G_equiv n x)).val
  rw [resH_eq_periodEquiv]

theorem resHLit_bijective (n : ℕ) : Function.Bijective (resHLit n) := by
  have : (resHLit n : _ → _) = resHLitEquiv n := funext fun x => (resHLitEquiv_apply n x).symm
  rw [this]
  exact (resHLitEquiv n).bijective

/-- **The class of the residue cycle `F_q`**: the inverse of the literal residue. -/
def residueClass (n : ℕ) : OrdinaryResiduePeriod.periodSpace (n + 1) ≃ₗ[ℚ] groupHomology (ResRep n) 3 :=
  (resHLitEquiv n).symm

theorem resHLit_residueClass (n : ℕ) (q : OrdinaryResiduePeriod.periodSpace (n + 1)) :
    resHLit n (residueClass n q) = q := by
  rw [← resHLitEquiv_apply]
  exact (resHLitEquiv n).apply_symm_apply q

/-- **Lemma 4.5, sentence 1**, on literal group homology.  For every `q ∈ ℬ_{n+1}` there is a unique class
`x ∈ H₃(G, ℛ_n ⊗ det)` whose literal residue is `q`; its Steinberg functional takes the value `F_q` at the identity apartment. -/
theorem lemma_4_5_residue_cycle (n : ℕ) (q : OrdinaryResiduePeriod.periodSpace (n + 1)) :
    ∃! x : groupHomology (ResRep n) 3, resHLit n x = q ∧
      (H3_G_equiv n x).val (OrdinaryApartmentPresentation.frameCycle 1) = Fq n q := by
  refine ⟨residueClass n q, ⟨resHLit_residueClass n q, ?_⟩, ?_⟩
  · rw [value_eq_Fq, resHLit_residueClass]
  · rintro y ⟨hy, -⟩
    apply (resHLit_bijective n).1
    rw [hy, resHLit_residueClass]

/-- The inverse of the identification reads the literal residue at `a = 0`, namely `q(b,c)`. -/
theorem residue_at_a_eq_zero (n : ℕ) (x : groupHomology (ResRep n) 3) :
    ((resHLit n x).val : BinaryV (n + 1)) =
      SinglePoleCoordinate.literalFiberMap n 0
        ((H3_G_equiv n x).val (OrdinaryApartmentPresentation.frameCycle 1) (axis 0)) := by
  rw [value_eq_Fq]
  have := Fq_coordinate n (resHLit n x) 0
  exact this.symm

end TernaryPeriodPolynomials.Argument.Lemma45Literal
