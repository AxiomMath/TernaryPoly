module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HodgeFormDict
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.CuspFromL2

@[expose] public section


/-!
# Cusp forms from a smooth closed and co-closed form of finite energy

Foundation file of the unconditional Eichler--Shimura route.  Composition of `decoupling_of_pair` with `CuspL2.cuspForm_of_L2`: the output of the `L²`
Hodge projection and Weyl's lemma for `Sym^m` is the sum of two Mathlib cusp forms of weight
`m + 2`, `a - i b = 2 F(z) E_m(z)` and `a + i b = 2 conj (G(z)) E_0(z)` in the Hodge frame
(`cuspForms_of_pair`).

Formalized by Claude Sonnet 5.5.
-/

open Complex Matrix MeasureTheory UpperHalfPlane ModularForm
open scoped MatrixGroups ContDiff
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (cutoff IsCover)
open TernaryPeriodPolynomials.Argument.ESFoundations.L2 (Wd)
open TernaryPeriodPolynomials.Argument.ESFoundations.Weyl (dir)

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame

variable {m : ℕ} {Γ : Subgroup SL(2, ℤ)}

/-- **Cusp forms from the Hodge decoupling.**  Under the hypotheses of `decoupling_of_pair`, for
`m ≥ 1` and `-1 ∉ Γ`, there are Mathlib cusp forms `F, G` of weight `m + 2` for the image of `Γ`
in `GL₂(ℝ)` whose values give the `dz` and `dz̄` coefficients of the form in the Hodge frame. -/
theorem cuspForms_of_pair [Γ.FiniteIndex] (hm : 1 ≤ m) (hneg : (-1 : SL(2, ℤ)) ∉ Γ)
    {R : Finset SL(2, ℤ)} (hR : IsCover Γ R)
    {a b : ℂ → Wd (m + 1)} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hcl : ∀ z ∈ U, fderiv ℝ b z (dir 0) = fderiv ℝ a z (dir 1))
    (hco : ∀ z ∈ U, fderiv ℝ (fun z => (hodgeDatumSym m Γ).H z (a z)) z (dir 0) +
      fderiv ℝ (fun z => (hodgeDatumSym m Γ).H z (b z)) z (dir 1) = 0)
    (hE : (hodgeDatumSym m Γ).Eqv (formOfPair a b))
    (hen : Integrable (fun z => if z ∈ U then
      cutoff Γ R z * (hodgeDatumSym m Γ).edens (formOfPair a b) z else 0)) :
    ∃ F G : CuspForm (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) ((m + 2 : ℕ) : ℤ),
      ∀ τ : ℍ, coefA a b (τ : ℂ) = F τ • (fun i => frameE m (τ : ℂ) i (Fin.last m)) ∧
        coefB a b (τ : ℂ) = starRingEnd ℂ (G τ) • (fun i => frameE m (τ : ℂ) i 0) := by
  obtain ⟨f, g, hf, hg, hfm, hgm, hfi, hgi, hrep⟩ := decoupling_of_pair hR ha hb hcl hco hE hen
  obtain ⟨F, hF⟩ := CuspL2.cuspForm_of_L2 hm hneg hR hf hfm hfi
  obtain ⟨G, hG⟩ := CuspL2.cuspForm_of_L2 hm hneg hR hg hgm hgi
  refine ⟨F, G, fun τ => ?_⟩
  have h := hrep (τ : ℂ) τ.im_pos
  rw [hF τ, hG τ]
  exact h

end TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
