module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalFlip
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalMaps

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory

/-- Inversion of the vertical isomorphisms preserves an actual commuting square. -/
theorem isoSquare_inverse {C : Type*} [Category* C] {A B X Y : C}
    (a : A ≅ X) (b : B ≅ Y) (f : A ⟶ B) (g : X ⟶ Y)
    (h : f ≫ b.hom = a.hom ≫ g) : g ≫ b.inv = a.inv ≫ f := by
  apply (cancel_epi a.hom).mp
  rw [←Category.assoc,←h,Category.assoc,Iso.hom_inv_id,Category.comp_id,
    ←Category.assoc,Iso.hom_inv_id,Category.id_comp]

variable {K L : RealBicomplex} (f : K ⟶ L)

/-- The actual signed axis flip is natural for genuine bicomplex maps. -/
theorem totalFlipIso_naturality :
    totalWindowMap f ≫ (totalFlipIso L).hom = (totalFlipIso K).hom ≫
      totalWindowMap ((HomologicalComplex₂.flipFunctor (ModuleCat ℝ)
        (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map f) := by
  apply ShortComplex.Hom.ext
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    apply Prod.ext
    · exact (map_neg (bicomplexMap f 1 1) x.2.1).symm
    · rfl
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The induced signed total homology flip is natural for the actual total maps. -/
theorem totalFlipHomologyIso_naturality :
    ShortComplex.homologyMap (totalWindowMap f) ≫ (totalFlipHomologyIso L).hom =
      (totalFlipHomologyIso K).hom ≫ ShortComplex.homologyMap
        (totalWindowMap ((HomologicalComplex₂.flipFunctor (ModuleCat ℝ)
          (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map f)) := by
  exact (ShortComplex.homologyMap_comp _ _).symm.trans
    ((congrArg (fun u : totalWindow K ⟶ totalWindow L.flip => ShortComplex.homologyMap u)
      (totalFlipIso_naturality f)).trans (ShortComplex.homologyMap_comp _ _))

/-- Inverse signed total flips preserve the actual naturality square. -/
theorem totalFlipHomologyIso_inv_naturality :
    ShortComplex.homologyMap (totalWindowMap ((HomologicalComplex₂.flipFunctor (ModuleCat ℝ)
      (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map f)) ≫ (totalFlipHomologyIso L).inv =
        (totalFlipHomologyIso K).inv ≫ ShortComplex.homologyMap (totalWindowMap f) :=
  isoSquare_inverse (totalFlipHomologyIso K) (totalFlipHomologyIso L)
    (ShortComplex.homologyMap (totalWindowMap f))
    (ShortComplex.homologyMap (totalWindowMap ((HomologicalComplex₂.flipFunctor (ModuleCat ℝ)
      (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map f))) (totalFlipHomologyIso_naturality f)

end TernaryPoly.SmoothSingularGlobal
