module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.FaceCarriers
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.NerveLabels

@[expose] public section


/-!
# Strata maps of the model cone are quasi-isomorphisms

A chain map from the model resolution `ℚ[V^{•+1} × ι]` to the equivariant singular chains of a sum space `Σ i, X i`
(`X i` contractible), which is carried by the label fibres in degree `0` and compatible with the augmentations to the
trivial representation, is a quasi-isomorphism: it commutes with the augmentations to the permutation module
`ℚ[ι]`, which are quasi-isomorphisms on both sides.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly TernaryPoly.EquivariantSingularResolution
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.SingularComponentAugmentation (Total)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

theorem toSingle₀_ext {Γ : Type} [Group Γ] {C : ChainComplex (Rep.{0} ℚ Γ) ℕ} {M : Rep.{0} ℚ Γ}
    {φ ψ : C ⟶ (ChainComplex.single₀ (Rep.{0} ℚ Γ)).obj M} (h : φ.f 0 = ψ.f 0) : φ = ψ :=
  (ChainComplex.toSingle₀Equiv C M).injective (Subtype.ext (by simpa using h))

variable {G : Type} [Group G] {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)]
  [∀ i, ContractibleSpace (X i)] [TopologicalSpace ι] [DiscreteTopology ι] [MulAction G ι]
  [MulAction G (Total X)] [ContinuousConstSMul G (Total X)]
  (hlabel : ∀ (g : G) (x : Total X), (g • x).1 = g • x.1)

theorem sigma_stratum_quasiIso (V : Type) [MulAction G V] (hfree : ∀ (γ : G) (v : V), γ • v = v → γ = 1) (v₀ : V)
    (w : prodComplex G V ι ⟶ equivariantChains G (TopCat.of (Total X)))
    (hc : ∀ s : (nerveCells G V ι hfree).S 0, (w.f 0).hom ((nerveCells G V ι hfree).cell 0 s) ∈
      (LabelData.ofSigma (G := G) X hlabel).faceK (nerveLab G V ι hfree 0 s) 0)
    (he : ∀ x, (singEps (G := G) (TopCat.of (Total X))).hom ((w.f 0).hom x) = (nerveEps G V ι).hom x) :
    QuasiIso w := by
  have hπ : QuasiIso (prodEpsToSingle G V ι v₀) := (prodResolution G V ι v₀ hfree).quasiIso
  have hπ' : QuasiIso (SingularComponentAugmentation.augmentationChain X G hlabel) := inferInstance
  have hcomp : w ≫ SingularComponentAugmentation.augmentationChain X G hlabel = prodEpsToSingle G V ι v₀ := by
    apply toSingle₀_ext
    have e1 : (prodEpsToSingle G V ι v₀).f 0 = prodEps G V ι :=
      ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
    rw [e1, HomologicalComplex.comp_f, SingularComponentAugmentation.augmentationChain_f_zero]
    apply (nerveCells G V ι hfree).hom_ext 0
    intro s
    have hy := hc s
    have h1 := scalarAug_of_mem_faceK X hlabel _ hy
    have h2 := he ((nerveCells G V ι hfree).cell 0 s)
    have h3 : (nerveEps G V ι).hom ((nerveCells G V ι hfree).cell 0 s) = (1 : ℚ) :=
      nerveEps_single G V ι (show (Fin (0+1) → V) × ι from s)
    have h4 : epsL (G := G) (TopCat.of (Total X)) ((w.f 0).hom ((nerveCells G V ι hfree).cell 0 s)) = 1 :=
      h2.trans h3
    have h5 := prodEps_single G V ι (show (Fin (0+1) → V) × ι from s).1 (show (Fin (0+1) → V) × ι from s).2
    change (SingularComponentAugmentation.augmentation X G hlabel).hom ((w.f 0).hom _) = _
    change (SingularComponentAugmentation.scalarAugmentation X).hom
      ((w.f 0).hom ((nerveCells G V ι hfree).cell 0 s)) = _
    rw [h1, h4, one_smul]
    exact h5.symm
  have : QuasiIso (w ≫ SingularComponentAugmentation.augmentationChain X G hlabel) := by
    rw [hcomp]; exact hπ
  exact quasiIso_of_comp_right w (SingularComponentAugmentation.augmentationChain X G hlabel)

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
