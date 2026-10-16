module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalWindow
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits

variable {K : RealBicomplex} {C : CochainComplex (ModuleCat.{0} ℝ) ℕ}

/-- An actual augmentation into column zero, annihilated by the first horizontal differential. -/
structure TotalAugmentation (C : CochainComplex (ModuleCat.{0} ℝ) ℕ) (K : RealBicomplex) where
  map : C ⟶ K.X 0
  horizontal_zero : map ≫ K.d 0 1 = 0

namespace TotalAugmentation

variable (a : TotalAugmentation C K)

/-- Degreewise augmentation. -/
abbrev augment (q : ℕ) := (a.map.f q).hom

/-- The augmentation is horizontally closed. -/
theorem augment_horizontal (q : ℕ) (x : C.X q) :
    horizontal K 0 q (a.augment q x) = 0 :=
  congrArg (fun f => (f.f q).hom x) a.horizontal_zero

/-- The augmentation commutes with the actual vertical differentials. -/
theorem augment_vertical (q : ℕ) (x : C.X q) :
    vertical K 0 q (a.augment q x) = a.augment (q+1) ((C.d q (q+1)).hom x) :=
  congrArg (fun f => f.hom x) (a.map.comm q (q+1))

/-- Literal insertion in total degree one. -/
def augmentationOne : C.X 1 →ₗ[ℝ] TotalOne K :=
  (0 : C.X 1 →ₗ[ℝ] (K.X 1).X 0).prod (a.augment 1)

/-- Literal insertion in total degree two. -/
def augmentationTwo : C.X 2 →ₗ[ℝ] TotalTwo K :=
  (0 : C.X 2 →ₗ[ℝ] (K.X 2).X 0).prod
    ((0 : C.X 2 →ₗ[ℝ] (K.X 1).X 1).prod (a.augment 2))

/-- Literal insertion in total degree three. -/
def augmentationThree : C.X 3 →ₗ[ℝ] TotalThree K :=
  (0 : C.X 3 →ₗ[ℝ] (K.X 3).X 0).prod
    ((0 : C.X 3 →ₗ[ℝ] (K.X 2).X 1).prod
      ((0 : C.X 3 →ₗ[ℝ] (K.X 1).X 2).prod (a.augment 3)))

/-- The first literal insertion commutes with the signed total differential. -/
theorem augmentationOne_d (x : C.X 1) :
    totalOneD K (a.augmentationOne x) = a.augmentationTwo ((C.d 1 2).hom x) := by
  change (horizontal K 1 0 0, -vertical K 1 0 0 + horizontal K 0 1 (a.augment 1 x),
    vertical K 0 1 (a.augment 1 x)) = (0, 0, a.augment 2 ((C.d 1 2).hom x))
  simp only [map_zero, neg_zero, zero_add, augment_horizontal, augment_vertical]

/-- The second literal insertion commutes with the signed total differential. -/
theorem augmentationTwo_d (x : C.X 2) :
    totalTwoD K (a.augmentationTwo x) = a.augmentationThree ((C.d 2 3).hom x) := by
  change (horizontal K 2 0 0, vertical K 2 0 0 + horizontal K 1 1 0,
    -vertical K 1 1 0 + horizontal K 0 2 (a.augment 2 x),
    vertical K 0 2 (a.augment 2 x)) = (0, 0, 0, a.augment 3 ((C.d 2 3).hom x))
  simp only [map_zero, neg_zero, zero_add, augment_horizontal, augment_vertical]

/-- The actual degree-two comparison map into the total short complex. -/
def totalAugmentationMap : C.sc' 1 2 3 ⟶ totalWindow K where
  τ₁ := ModuleCat.ofHom a.augmentationOne
  τ₂ := ModuleCat.ofHom a.augmentationTwo
  τ₃ := ModuleCat.ofHom a.augmentationThree
  comm₁₂ := ModuleCat.hom_ext (LinearMap.ext fun x => a.augmentationOne_d x)
  comm₂₃ := ModuleCat.hom_ext (LinearMap.ext fun x => a.augmentationTwo_d x)

/-- Exactness hypotheses for actual augmented horizontal rows. They are later proved from
actual Čech contractions; no global comparison is included in this data. -/
structure ExactRows : Prop where
  injective : ∀ q, Function.Injective (a.augment q)
  augmentation_exact : ∀ q (x : (K.X 0).X q), horizontal K 0 q x = 0 →
    ∃ z : C.X q, a.augment q z = x
  horizontal_exact : ∀ p q (x : (K.X (p+1)).X q),
    horizontal K (p+1) q x = 0 → ∃ z : (K.X p).X q, horizontal K p q z = x

end TotalAugmentation
end TernaryPoly.SmoothSingularGlobal
