module

public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityRestrictionBar
public import Mathlib.RepresentationTheory.Coinduced

@[expose] public section

noncomputable section
open CategoryTheory HomologicalComplex
open scoped MonoidAlgebra TensorProduct
namespace TernaryPoly.SingularCoverRestriction

variable {G H : Type} [Group G] [Group H]

/-- The actual standard/bar comparison on a free generator retains the partial-product convention. -/
theorem barToStandard_generator (n : ℕ) (x : Fin n → G) (g : G) (r : ℚ) :
    ((Rep.barComplex.isoStandardComplex ℚ G).hom.f n).hom
        (Finsupp.single x (MonoidAlgebra.single g r))=
      MonoidAlgebra.single (g • Fin.partialProd x) r := by
  open Rep CategoryTheory.MonoidalCategory in
  change (diagonalSuccIsoFree ℚ G n).inv.hom
    (Finsupp.single x (MonoidAlgebra.single g r))=_
  simp only [Rep.diagonalSuccIsoFree,Rep.diagonalSuccIsoTensorTrivial,Iso.trans_inv,Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Rep.Hom.hom (Rep.leftRegularTensorTrivialIsoFree ℚ G (Fin n → G)).inv)
      (Finsupp.single x (MonoidAlgebra.single g r))=
        MonoidAlgebra.single g 1 ⊗ₜ[ℚ] MonoidAlgebra.single x r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r
  rw [step1]
  simp only [Action.tensorObj_V,Rep.tensor_V,Rep.tensor_ρ]
  have key₁ := Representation.linearizeMap_single (k := ℚ)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (g,x) ((1 : ℚ)*r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := ℚ)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) g x 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv) z) key₂).trans key₁).trans (by
      rw [one_mul]
      exact congrArg (fun t => MonoidAlgebra.single t r)
        (Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g x))

/-- The actual augmentation in degree zero, with its codomain exposed as the trivial module. -/
def barAugmentation : Rep.free ℚ G (Fin 0 → G) ⟶ Rep.trivial ℚ G ℚ :=
  (Rep.barResolution ℚ G).π.f 0

/-- The actual bar augmentation sends every free generator in degree zero to one. -/
theorem barAugmentation_generator (x : Fin 0 → G) :
    (barAugmentation (G := G)).hom
      (Finsupp.single x (MonoidAlgebra.single 1 1))=1 := by
  change (Rep.standardComplex.ε ℚ G).hom
    (((Rep.barComplex.isoStandardComplex ℚ G).hom.f 0).hom
      (Finsupp.single x (MonoidAlgebra.single 1 1)))=1
  rw [barToStandard_generator]
  simp [Rep.standardComplex.ε]

/-- The explicit bar map preserves the literal degree-zero augmentation. -/
theorem barDegreeMap_augmentation (φ : H →* G) :
    barDegreeMap φ 0 ≫ Rep.resMap φ ((Rep.barResolution ℚ G).π.f 0)=
      (Rep.barResolution ℚ H).π.f 0 := by
  apply Rep.free_ext
  intro x
  change ((Rep.barResolution ℚ G).π.f 0).hom
      ((barDegreeMap φ 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1)))=
    ((Rep.barResolution ℚ H).π.f 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))
  rw [barDegreeMap_generator]
  exact (barAugmentation_generator (φ ∘ x)).trans (barAugmentation_generator x).symm

/-- Restricting the target bar resolution along a subgroup gives an actual projective resolution. -/
def restrictedBarResolution (S : Subgroup G) : ProjectiveResolution (Rep.trivial ℚ S ℚ) :=
  (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution ℚ G)

/-- The explicit subgroup bar map preserves the complete augmentation of the restricted resolution. -/
theorem barMap_augmentation (S : Subgroup G) :
    barMap S.subtype ≫ (restrictedBarResolution S).π=(Rep.barResolution ℚ S).π := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change barDegreeMap S.subtype 0 ≫ Rep.resMap S.subtype ((Rep.barResolution ℚ G).π.f 0) ≫ _=_
  convert barDegreeMap_augmentation S.subtype using 1
  rfl

end TernaryPoly.SingularCoverRestriction
