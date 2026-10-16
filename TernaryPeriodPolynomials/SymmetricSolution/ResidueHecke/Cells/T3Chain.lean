module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.PushRG
public import TernaryPeriodPolynomials.GroupCohomology.Homology.ResolutionTransfer
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.T0Coeff
public import TernaryPeriodPolynomials.GroupCohomology.Homology.CosetSum

@[expose] public section


/-!
# Lemma B.1: the coefficient at `T₀` of the transfer of a cell generator

Formalized by Claude Sonnet 5.5.

`T3_chain`: for the `P_H`-chain `[a ⊗ ⟨T₀⟩]` of `(𝓡_{n,H₀} ⊗ RG₃)_{P_H}` (`⟨T₀⟩` the generator of the oriented cell `T₀`),
the `a = 0` component of the coefficient at `T₀` of its transfer to `P_N`, pushed to the cell complex of `Γ(6)`
(`Cmap`), is `[P_H : P_N]⁻¹ ∑_{h ∈ Stab_{P_H}(T₀)} ε(h) ρ(h) a` with `ε = cellSign` (`stabTerm`).  It combines
the explicit coefficient `comp0_coeffVal_lof` with the coset bookkeeping `coset_sum_eq` (`P_N` acts freely on the cells).
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
open TernaryPoly.OrdinaryResidueSupport (axis)
open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.HochschildSerre
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
open Finsupp
open scoped Classical

/-- The action of `P_H` on the cells of grade `n` through `GL₃(ℤ)`. -/
instance cellActPH (n : ℕ) : MulAction PH (Graded n) where
  smul g C := glGraded n g.1 C
  one_smul C := glGraded_one n C
  mul_smul g h C := glGraded_mul n g.1 h.1 C

/-- The generator of the oriented cell `T₀` in `RG₃`. -/
def genT0 : ((RG_projRes PH).complex.X 3).V := single T0g (1 : ℚ)

theorem term_value (n : ℕ) (s : PH) (a : ResidueFiber n (axis 0)) :
    component n (axis 0) ((coeffAtT0 (Rep.res principalSix.subtype (ResRep n))).hom
      (((pushRG n).f 3).hom (Coinvariants.mk
        ((((FibRep n) ⊗ (RG_projRes PH).complex.X 3).ρ).comp PN.subtype)
        (((FibRep n).ρ s a) ⊗ₜ[ℚ] (((RG_projRes PH).complex.X 3).ρ s genT0))))) =
      cellSign s.1 T0g.1.val •
        (if h : ∃ g : principalSix, (g : IntegralGL) ∈ PH ∧ g • (glGraded 3 s.1 T0g) = T0g then
          fiberAction n (h.choose : IntegralGL) (fiberAction n s.1 a) else 0) := by
  rw [pushRG_mk]
  have e1 : (((RG_projRes PH).complex.X 3).ρ s genT0) =
      single (glGraded 3 s.1 T0g) (cellSign s.1 T0g.1.val * 1) := twistLin_single 3 s.1 T0g 1
  rw [e1]
  have e2 : (RG_resIso.hom.f 3).hom (single (glGraded 3 s.1 T0g) (cellSign s.1 T0g.1.val * 1)) =
      (cellSign s.1 T0g.1.val * 1) • (MonoidAlgebra.single (glGraded 3 s.1 T0g) (1 : ℚ)) := by
    change MonoidAlgebra.single (glGraded 3 s.1 T0g) (cellSign s.1 T0g.1.val * 1) = _
    rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one, mul_one]
  rw [e2, TensorProduct.tmul_smul, map_smul]
  have key := (coeffAtT0 (Rep.res principalSix.subtype (ResRep n))).hom.map_smul (cellSign s.1 T0g.1.val * 1)
    (Coinvariants.mk ((Rep.res principalSix.subtype (ResRep n)).ρ.tprod (cellRep 3).ρ)
      ((Rep.Hom.hom (lofN n)) (((FibRep n).ρ s) a) ⊗ₜ[ℚ] MonoidAlgebra.single (glGraded 3 (↑s) T0g) (1 : ℚ)))
  erw [key, map_smul]
  change (cellSign s.1 T0g.1.val * 1) • component n (axis 0) ((coeffAtT0 (Rep.res principalSix.subtype (ResRep n))).hom
    (Rep.coinvariantsTensorMk (Rep.res principalSix.subtype (ResRep n)) (cellRep 3)
      (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) (fiberAction n s.1 a))
      (MonoidAlgebra.single (glGraded 3 s.1 T0g) 1))) = _
  rw [coeffAtT0_mk, comp0_coeffVal_lof, mul_one]

/-- The contribution of an element `h` of the stabilizer: `ε(h) ρ(h) a`. -/
def stabTerm (n : ℕ) (a : ResidueFiber n (axis 0)) (h : PH) : ResidueFiber n (axis 0) :=
  cellSign h.1 T0g.1.val • fiberAction n h.1 a

theorem coset_term (n : ℕ) (a : ResidueFiber n (axis 0)) (x : PH ⧸ PN) :
    component n (axis 0) ((coeffAtT0 (Rep.res principalSix.subtype (ResRep n))).hom
      (((pushRG n).f 3).hom (Coinvariants.mk
        ((((FibRep n) ⊗ (RG_projRes PH).complex.X 3).ρ).comp PN.subtype)
        (((FibRep n).ρ x.out a) ⊗ₜ[ℚ] (((RG_projRes PH).complex.X 3).ρ x.out genT0))))) =
      (if (∃ g ∈ PN, glGraded 3 g.1 (glGraded 3 x.out.1 T0g) = T0g) then
        stabTerm n a (cosetElt PN T0g T0g x) else 0) := by
  rw [term_value]
  by_cases hex : ∃ g ∈ PN, glGraded 3 g.1 (glGraded 3 x.out.1 T0g) = T0g
  · rw [ite_eq_left hex]
    obtain ⟨hgN, hg⟩ := hex.choose_spec
    set g1 := hex.choose with hg1
    have h' : ∃ g : principalSix, (g : IntegralGL) ∈ PH ∧ g • (glGraded 3 x.out.1 T0g) = T0g :=
      ⟨⟨g1.1, hgN⟩, g1.2, by rw [← glGraded_six]; exact hg⟩
    rw [dite_eq_left h']
    have hch : h'.choose = ⟨g1.1, hgN⟩ := by
      have h2 := h'.choose_spec.2
      refine translate_unique _ _ (glGraded 3 x.out.1 T0g).1 (congrArg Subtype.val h2) ?_
      exact congrArg Subtype.val (show (⟨g1.1, hgN⟩ : principalSix) • (glGraded 3 x.out.1 T0g) = T0g by
        rw [← glGraded_six]; exact hg)
    rw [hch]
    have hce : cosetElt PN T0g T0g x = g1 * x.out := by
      have hex' : ∃ g ∈ PN, g • ((x.out : PH) • T0g) = T0g := hex
      unfold cosetElt
      rw [dite_eq_left hex']
    rw [hce, stabTerm]
    have hsg : cellSign (g1.1 * x.out.1) T0g.1.val = cellSign x.out.1 T0g.1.val := by
      rw [cellSign_cell_mul, cellSign_six ⟨g1.1, hgN⟩, one_mul]
    show cellSign x.out.1 T0g.1.val • fiberAction n g1.1 (fiberAction n x.out.1 a) =
      cellSign (g1.1 * x.out.1) T0g.1.val • fiberAction n (g1.1 * x.out.1) a
    rw [hsg, fiberAction_mul n x.out.2 a]
  · rw [ite_eq_right hex]
    have h' : ¬ ∃ g : principalSix, (g : IntegralGL) ∈ PH ∧ g • (glGraded 3 x.out.1 T0g) = T0g := by
      rintro ⟨g, hgP, hg⟩
      exact hex ⟨⟨g.1, hgP⟩, g.2, by rw [glGraded_six]; exact hg⟩
    rw [dite_eq_right h', smul_zero]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The `a = 0` component of the coefficient at `T₀` of the pushed-forward cell chain. -/
def Cmap (n : ℕ) : (CxN PN (YAR (RG_projRes PH) (FibRep n))).X 3 →ₗ[ℚ] ResidueFiber n (axis 0) :=
  (component n (axis 0)).comp ((coeffAtT0 (Rep.res principalSix.subtype (ResRep n))).hom.comp
    ((pushRG n).f 3).hom)

theorem T3_chain (n : ℕ) (a : ResidueFiber n (axis 0)) (S : Finset PH)
    (hS : ∀ h, h ∈ S ↔ glGraded 3 h.1 T0g = T0g) :
    Cmap n (((trY PN (YAR (RG_projRes PH) (FibRep n))).f 3).hom
      (Coinvariants.mk (((FibRep n) ⊗ (RG_projRes PH).complex.X 3).ρ)
        (a ⊗ₜ[ℚ] genT0))) =
      (Fintype.card (PH ⧸ PN) : ℚ)⁻¹ • ∑ h ∈ S, stabTerm n a h := by
  have e : ((trY PN (YAR (RG_projRes PH) (FibRep n))).f 3).hom
      (Coinvariants.mk (((FibRep n) ⊗ (RG_projRes PH).complex.X 3).ρ) (a ⊗ₜ[ℚ] genT0)) =
      (Fintype.card (PH ⧸ PN) : ℚ)⁻¹ • ∑ x : PH ⧸ PN, Coinvariants.mk
        ((((FibRep n) ⊗ (RG_projRes PH).complex.X 3).ρ).comp PN.subtype)
        (((FibRep n).ρ x.out a) ⊗ₜ[ℚ] (((RG_projRes PH).complex.X 3).ρ x.out genT0)) := by
    have h1 := tMap_mk PN ((YAR (RG_projRes PH) (FibRep n)).X 3).ρ ((Fintype.card (PH ⧸ PN) : ℚ)⁻¹)
      (a ⊗ₜ[ℚ] genT0 : ((YAR (RG_projRes PH) (FibRep n)).X 3).V)
    have h2 := tSum_apply PN ((YAR (RG_projRes PH) (FibRep n)).X 3).ρ
      (a ⊗ₜ[ℚ] genT0 : ((YAR (RG_projRes PH) (FibRep n)).X 3).V)
    exact h1.trans (congrArg (fun z => (Fintype.card (PH ⧸ PN) : ℚ)⁻¹ • z) h2)
  rw [e]
  erw [map_smul, map_sum]
  congr 1
  let _ : MulAction PH (Graded 3) := cellActPH 3
  have hfree : ∀ g ∈ PN, g • T0g = T0g → g = 1 := by
    intro g hg hgT
    have h1 : (⟨g.1, hg⟩ : principalSix) • T0g = T0g := by
      rw [← glGraded_six]
      exact hgT
    have := translate_unique ⟨g.1, hg⟩ 1 T0g.1 (congrArg Subtype.val h1)
      (congrArg Subtype.val (one_smul principalSix T0g))
    apply Subtype.ext
    have h2 := congrArg Subtype.val this
    exact h2
  have key := coset_sum_eq PN T0g T0g hfree (stabTerm n a) S hS
  rw [← key]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact coset_term n a x

end TernaryPeriodPolynomials.Argument.AppendixBResidue
