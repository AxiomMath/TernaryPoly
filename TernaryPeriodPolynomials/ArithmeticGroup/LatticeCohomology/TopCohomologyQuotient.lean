module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.TopCohomologyResolution

@[expose] public section


open CategoryTheory CategoryTheory.Limits

noncomputable section
namespace TernaryPoly.LatticeTopCohomology

variable (A : Rep ℚ Lattice)

def relations : Submodule ℚ A :=
  LinearMap.range (A.ρ first - LinearMap.id) ⊔ LinearMap.range (A.ρ second - LinearMap.id)

abbrev homComplex := resolution.complex.linearYonedaObj ℚ A

/-- Evaluation at the unique regular generator is the degree-two Hom coordinate. -/
abbrev topCoordinate : ((homComplex A).X 2) ≃ₗ[ℚ] A := Rep.leftRegularHomEquiv A

/-- Evaluation at the two free edge generators is the degree-one Hom coordinate. -/
abbrev edgeCoordinate : ((homComplex A).X 1) ≃ₗ[ℚ] (Fin 2 → A) :=
  Rep.freeLiftLEquiv ℚ Lattice (Fin 2) A

theorem equivariant_single (f : P₁ ⟶ A) (i : Fin 2) (g : Lattice) :
    f.hom (Finsupp.single i (MonoidAlgebra.single g 1)) =
      A.ρ g (f.hom (Finsupp.single i (MonoidAlgebra.single 1 1))) := by
  obtain ⟨v, rfl⟩ := (Rep.freeLiftLEquiv ℚ Lattice (Fin 2) A).symm.surjective f
  change Representation.freeLift A.ρ v (Finsupp.single i (MonoidAlgebra.single g 1)) =
    A.ρ g (Representation.freeLift A.ρ v (Finsupp.single i (MonoidAlgebra.single 1 1)))
  simp

/-- The degree-two Hom differential has the exact signed Koszul formula. -/
theorem top_differential (f : P₁ ⟶ A) :
    topCoordinate A (((homComplex A).d 1 2).hom f) =
      (edgeCoordinate A f) 0 + A.ρ first ((edgeCoordinate A f) 1) -
        A.ρ second ((edgeCoordinate A f) 0) - (edgeCoordinate A f) 1 := by
  change f.hom (d₂.hom (MonoidAlgebra.single 1 1)) = _
  rw [d₂_single]
  simp only [one_smul, one_mul, map_sub, map_add]
  rw [equivariant_single A f 1 first, equivariant_single A f 0 second]
  rfl

/-- Top coboundaries are precisely the sum of the two actual coefficient difference ranges. -/
theorem top_range :
    (LinearMap.range ((homComplex A).d 1 2).hom).map (topCoordinate A).toLinearMap = relations A := by
  apply le_antisymm
  · rintro x ⟨y, ⟨f, rfl⟩, rfl⟩
    change topCoordinate A (((homComplex A).d 1 2).hom f) ∈ relations A
    rw [top_differential A f]
    have h₁ : A.ρ first ((edgeCoordinate A f) 1) - (edgeCoordinate A f) 1 ∈
        LinearMap.range (A.ρ first - LinearMap.id) := ⟨(edgeCoordinate A f) 1, rfl⟩
    have h₂ : (edgeCoordinate A f) 0 - A.ρ second ((edgeCoordinate A f) 0) ∈
        LinearMap.range (A.ρ second - LinearMap.id) := by
      refine ⟨-((edgeCoordinate A f) 0), ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_neg]
      abel
    convert Submodule.add_mem_sup h₁ h₂ using 1 <;> abel
  · apply sup_le
    · rintro x ⟨v, rfl⟩
      let f := (edgeCoordinate A).symm ![0,v]
      refine ⟨((homComplex A).d 1 2).hom f, ⟨f,rfl⟩, ?_⟩
      change topCoordinate A (((homComplex A).d 1 2).hom f) = _
      rw [top_differential A f]
      simp [f, sub_eq_add_neg, add_comm]
    · rintro x ⟨v, rfl⟩
      let f := (edgeCoordinate A).symm ![-v,0]
      refine ⟨((homComplex A).d 1 2).hom f, ⟨f,rfl⟩, ?_⟩
      change topCoordinate A (((homComplex A).d 1 2).hom f) = _
      rw [top_differential A f]
      simp [f, sub_eq_add_neg, add_comm]

theorem top_outgoing_zero : (homComplex A).d 2 3 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (0 : PZero ⟶ P₂) ≫ f = 0
  exact zero_comp

/-- The abstract Hom-complex top homology is the actual coefficient coinvariant quotient. -/
def homologyQuotientIso : (homComplex A).homology 2 ≅ ModuleCat.of ℚ (A ⧸ relations A) :=
  (homComplex A).homologyIsoSc' 1 2 3 (by simp) (by simp) ≪≫
    (ShortComplex.LeftHomologyData.ofHasCokernel ((homComplex A).sc' 1 2 3)
      (top_outgoing_zero A)).homologyIso ≪≫
    ModuleCat.cokernelIsoRangeQuotient ((homComplex A).d 1 2) ≪≫
    (Submodule.Quotient.equiv _ _ (topCoordinate A) (top_range A)).toModuleIso

/-- Genuine rank-two lattice group cohomology in degree two is the coinvariant quotient. -/
def groupCohomologyQuotientIso : groupCohomology A 2 ≅ ModuleCat.of ℚ (A ⧸ relations A) :=
  groupCohomologyIso A 2 resolution ≪≫ homologyQuotientIso A

end TernaryPoly.LatticeTopCohomology
