module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory

variable {K L : RealBicomplex} (f : K ⟶ L)

/-- The component linear map of an actual bicomplex morphism. -/
abbrev bicomplexMap (p q : ℕ) := ((f.f p).f q).hom

theorem bicomplexMap_horizontal (p q : ℕ) (x : (K.X p).X q) :
    horizontal L p q (bicomplexMap f p q x) = bicomplexMap f (p+1) q (horizontal K p q x) :=
  congrArg (fun k => (k.f q).hom x) (f.comm p (p+1))

theorem bicomplexMap_vertical (p q : ℕ) (x : (K.X p).X q) :
    vertical L p q (bicomplexMap f p q x) = bicomplexMap f p (q+1) (vertical K p q x) :=
  congrArg (fun k => k.hom x) ((f.f p).comm q (q+1))

/-- Literal degree-one total map. -/
def totalOneMap : TotalOne K →ₗ[ℝ] TotalOne L :=
  (bicomplexMap f 1 0).prodMap (bicomplexMap f 0 1)

/-- Literal degree-two total map. -/
def totalTwoMap : TotalTwo K →ₗ[ℝ] TotalTwo L :=
  (bicomplexMap f 2 0).prodMap ((bicomplexMap f 1 1).prodMap (bicomplexMap f 0 2))

/-- Literal degree-three total map. -/
def totalThreeMap : TotalThree K →ₗ[ℝ] TotalThree L :=
  (bicomplexMap f 3 0).prodMap ((bicomplexMap f 2 1).prodMap
    ((bicomplexMap f 1 2).prodMap (bicomplexMap f 0 3)))

/-- Actual totalization commutes with the first signed differential. -/
theorem totalOneMap_d (x : TotalOne K) : totalOneD L (totalOneMap f x) = totalTwoMap f (totalOneD K x) := by
  rcases x with ⟨a,b⟩
  apply Prod.ext
  · exact bicomplexMap_horizontal f 1 0 a
  apply Prod.ext
  · change -vertical L 1 0 (bicomplexMap f 1 0 a) + horizontal L 0 1 (bicomplexMap f 0 1 b) =
      bicomplexMap f 1 1 (-vertical K 1 0 a + horizontal K 0 1 b)
    rw [map_add,map_neg,bicomplexMap_vertical,bicomplexMap_horizontal]
  · exact bicomplexMap_vertical f 0 1 b

/-- Actual totalization commutes with the second signed differential. -/
theorem totalTwoMap_d (x : TotalTwo K) : totalTwoD L (totalTwoMap f x) = totalThreeMap f (totalTwoD K x) := by
  rcases x with ⟨a,b,c⟩
  apply Prod.ext
  · exact bicomplexMap_horizontal f 2 0 a
  apply Prod.ext
  · change vertical L 2 0 (bicomplexMap f 2 0 a) + horizontal L 1 1 (bicomplexMap f 1 1 b) =
      bicomplexMap f 2 1 (vertical K 2 0 a + horizontal K 1 1 b)
    rw [map_add,bicomplexMap_vertical,bicomplexMap_horizontal]
  apply Prod.ext
  · change -vertical L 1 1 (bicomplexMap f 1 1 b) + horizontal L 0 2 (bicomplexMap f 0 2 c) =
      bicomplexMap f 1 2 (-vertical K 1 1 b + horizontal K 0 2 c)
    rw [map_add,map_neg,bicomplexMap_vertical,bicomplexMap_horizontal]
  · exact bicomplexMap_vertical f 0 2 c

/-- The actual morphism between signed degree-two total windows. -/
def totalWindowMap : totalWindow K ⟶ totalWindow L where
  τ₁ := ModuleCat.ofHom (totalOneMap f)
  τ₂ := ModuleCat.ofHom (totalTwoMap f)
  τ₃ := ModuleCat.ofHom (totalThreeMap f)
  comm₁₂ := ModuleCat.hom_ext (LinearMap.ext (totalOneMap_d f))
  comm₂₃ := ModuleCat.hom_ext (LinearMap.ext (totalTwoMap_d f))

/-- Actual commuting column augmentations induce a literal commuting total-window square. -/
theorem totalAugmentationMap_naturality
    {A B : CochainComplex (ModuleCat.{0} ℝ) ℕ}
    (a : TotalAugmentation A K) (b : TotalAugmentation B L) (g : A ⟶ B)
    (h : a.map ≫ f.f 0 = g ≫ b.map) :
    a.totalAugmentationMap ≫ totalWindowMap f =
      (HomologicalComplex.shortComplexFunctor' (ModuleCat ℝ) (ComplexShape.up ℕ) 1 2 3).map g ≫
        b.totalAugmentationMap := by
  have hn (n : ℕ) (x : A.X n) : bicomplexMap f 0 n (a.augment n x) =
      b.augment n ((g.f n).hom x) := congrArg (fun k => (k.f n).hom x) h
  apply ShortComplex.Hom.ext
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (bicomplexMap f 1 0 0,bicomplexMap f 0 1 (a.augment 1 x)) =
      (0,b.augment 1 ((g.f 1).hom x))
    rw [map_zero]
    exact congrArg (fun z => (0,z)) (hn 1 x)
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (bicomplexMap f 2 0 0,bicomplexMap f 1 1 0,bicomplexMap f 0 2 (a.augment 2 x)) =
      (0,0,b.augment 2 ((g.f 2).hom x))
    rw [map_zero,map_zero]
    exact congrArg (fun z => (0,0,z)) (hn 2 x)
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (bicomplexMap f 3 0 0,bicomplexMap f 2 1 0,bicomplexMap f 1 2 0,
      bicomplexMap f 0 3 (a.augment 3 x)) = (0,0,0,b.augment 3 ((g.f 3).hom x))
    rw [map_zero,map_zero,map_zero]
    exact congrArg (fun z => (0,0,0,z)) (hn 3 x)

end TernaryPoly.SmoothSingularGlobal
