module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVHomologyMaps

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalHomology SingularLocalExcision EquivariantSingularMayerVietoris
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (W : Rep.{0} ℚ G)
  (U D : Opens B) (hUD : U ⊔ D = ⊤) [IsCancelSMul G E]

/-- Actual small coefficient homology identifies with actual ambient local homology. -/
def ordinaryAmbientIso (b : ℕ) :
    ((ordinarySequence p W U D hUD).X₃).homology b ≅ (localChains p hp.out W).homology b :=
  isoOfQuasiIsoAt (smallToLocal p W U D hUD) b

/-- Homology of the actual pair splits into the two geometric local homology groups. -/
def ordinaryPairHomologyIso (b : ℕ) :
    (restrictedLocalChains p U W ⊞ restrictedLocalChains p D W).homology b ≅
      (restrictedLocalChains p U W).homology b ⊞ (restrictedLocalChains p D W).homology b :=
  (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) b).mapBiprod _ _

/-- The signed pair of actual geometric homology inclusions. -/
def ordinaryDiagonal (b : ℕ) :
    (restrictedLocalChains p ((U : Set B) ∩ (D : Set B)) W).homology b ⟶
      (restrictedLocalChains p U W).homology b ⊞ (restrictedLocalChains p D W).homology b :=
  biprod.lift (homologyMap (nestedLocalInclusion p ((U : Set B) ∩ (D : Set B)) U Set.inter_subset_left W) b)
    (-homologyMap (nestedLocalInclusion p ((U : Set B) ∩ (D : Set B)) D Set.inter_subset_right W) b)

/-- The sum of the two actual geometric homology inclusions. -/
def ordinarySum (b : ℕ) :
    (restrictedLocalChains p U W).homology b ⊞ (restrictedLocalChains p D W).homology b ⟶
      (localChains p hp.out W).homology b :=
  biprod.desc (homologyMap (localInclusion p U W) b) (homologyMap (localInclusion p D W) b)

/-- Actual ordinary Mayer–Vietoris connecting, lowering positive homological degree. -/
def ordinaryConnecting (b : ℕ) :
    (localChains p hp.out W).homology (b+1) ⟶
      (restrictedLocalChains p ((U : Set B) ∩ (D : Set B)) W).homology b :=
  (ordinaryAmbientIso p W U D hUD (b+1)).inv ≫
    (ordinarySequence_shortExact p W U D hUD).δ (b+1) b rfl

/-- Ordinary Mayer–Vietoris segment centered on the actual pair. -/
def ordinaryMiddleSegment (b : ℕ) : ShortComplex (ModuleCat ℚ) :=
  transportShortComplex ((ordinarySequence p W U D hUD).map
    (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) b))
    (Iso.refl _) (ordinaryPairHomologyIso p W U D b) (ordinaryAmbientIso p W U D hUD b)

/-- Ordinary Mayer–Vietoris segment centered on actual positive-degree ambient homology. -/
def ordinaryAmbientSegment (b : ℕ) : ShortComplex (ModuleCat ℚ) :=
  transportShortComplex (ShortComplex.mk _ _ ((ordinarySequence_shortExact p W U D hUD).comp_δ (b+1) b rfl))
    (ordinaryPairHomologyIso p W U D (b+1)) (ordinaryAmbientIso p W U D hUD (b+1)) (Iso.refl _)

/-- Ordinary Mayer–Vietoris segment centered on actual intersection homology. -/
def ordinaryIntersectionSegment (b : ℕ) : ShortComplex (ModuleCat ℚ) :=
  transportShortComplex (ShortComplex.mk _ _ ((ordinarySequence_shortExact p W U D hUD).δ_comp (b+1) b rfl))
    (ordinaryAmbientIso p W U D hUD (b+1)) (Iso.refl _) (ordinaryPairHomologyIso p W U D b)

/-- Exactness at the two genuine open homology groups in every degree. -/
theorem ordinaryMiddleSegment_exact (b : ℕ) : (ordinaryMiddleSegment p W U D hUD b).Exact :=
  ShortComplex.exact_of_iso (transportShortComplexIso _ _ _ _)
    ((ordinarySequence_shortExact p W U D hUD).homology_exact₂ b)

/-- Exactness at genuine ambient homology in every positive degree. -/
theorem ordinaryAmbientSegment_exact (b : ℕ) : (ordinaryAmbientSegment p W U D hUD b).Exact :=
  ShortComplex.exact_of_iso (transportShortComplexIso _ _ _ _)
    ((ordinarySequence_shortExact p W U D hUD).homology_exact₃ (b+1) b rfl)

/-- Exactness at genuine intersection homology in every degree. -/
theorem ordinaryIntersectionSegment_exact (b : ℕ) : (ordinaryIntersectionSegment p W U D hUD b).Exact :=
  ShortComplex.exact_of_iso (transportShortComplexIso _ _ _ _)
    ((ordinarySequence_shortExact p W U D hUD).homology_exact₁ (b+1) b rfl)

/-- The transported first arrow is literally the signed pair of geometric inclusions. -/
theorem ordinaryMiddleSegment_f (b : ℕ) :
    (ordinaryMiddleSegment p W U D hUD b).f = ordinaryDiagonal p W U D b := by
  change 𝟙 _ ≫ homologyMap (ordinarySequence p W U D hUD).f b ≫
    (ordinaryPairHomologyIso p W U D b).hom = _
  rw [Category.id_comp,ordinarySequence_f]
  change (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) b).map (biprod.lift _ _) ≫
    ((homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) b).mapBiprod _ _).hom = _
  erw [biprod.map_lift_mapBiprod]
  erw [Functor.map_neg]
  rfl

/-- The transported second arrow is literally the sum of geometric inclusions. -/
theorem ordinaryMiddleSegment_g (b : ℕ) :
    (ordinaryMiddleSegment p W U D hUD b).g = ordinarySum p W U D b := by
  change (ordinaryPairHomologyIso p W U D b).inv ≫
    homologyMap (ordinarySequence p W U D hUD).g b ≫ homologyMap (smallToLocal p W U D hUD) b = _
  erw [← homologyMap_comp]
  rw [ordinarySequence_g]
  exact biprod.mapBiprod_inv_map_desc (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) b) _ _ _ _

/-- The adjacent ambient segment retains the literal sum map. -/
theorem ordinaryAmbientSegment_f (b : ℕ) :
    (ordinaryAmbientSegment p W U D hUD b).f = ordinarySum p W U D (b+1) :=
  ordinaryMiddleSegment_g p W U D hUD (b+1)

/-- The ambient segment retains the actual connecting homomorphism. -/
theorem ordinaryAmbientSegment_g (b : ℕ) :
    (ordinaryAmbientSegment p W U D hUD b).g = ordinaryConnecting p W U D hUD b := by
  change _ ≫ _ ≫ 𝟙 _ = _
  exact congrArg (_ ≫ ·) (Category.comp_id _)

/-- The intersection segment retains the same actual connecting homomorphism. -/
theorem ordinaryIntersectionSegment_f (b : ℕ) :
    (ordinaryIntersectionSegment p W U D hUD b).f = ordinaryConnecting p W U D hUD b := by
  change _ ≫ _ ≫ 𝟙 _ = _
  exact congrArg (_ ≫ ·) (Category.comp_id _)

/-- The intersection segment retains the literal signed pair of inclusions. -/
theorem ordinaryIntersectionSegment_g (b : ℕ) :
    (ordinaryIntersectionSegment p W U D hUD b).g = ordinaryDiagonal p W U D b :=
  ordinaryMiddleSegment_f p W U D hUD b

include hUD in
/-- The actual ordinary sum is surjective in degree zero, completing the endpoint of the LES. -/
theorem ordinarySum_zero_epi : Epi (ordinarySum p W U D 0) := by
  have := (ordinarySequence_shortExact p W U D hUD).epi_g
  have : Epi (homologyMap (ordinarySequence p W U D hUD).g 0) :=
    epi_homologyMap_of_epi_of_not_rel _ 0 (by intro i hi; exact Nat.not_succ_le_zero i (Nat.le_of_eq hi))
  rw [← ordinaryMiddleSegment_g p W U D hUD 0]
  change Epi ((ordinaryPairHomologyIso p W U D 0).inv ≫
    homologyMap (ordinarySequence p W U D hUD).g 0 ≫ (ordinaryAmbientIso p W U D hUD 0).hom)
  have he := epi_comp (homologyMap (ordinarySequence p W U D hUD).g 0)
    (ordinaryAmbientIso p W U D hUD 0).hom
  exact @epi_comp (ModuleCat ℚ) _ _ _ _ (ordinaryPairHomologyIso p W U D 0).inv
    inferInstance (homologyMap (ordinarySequence p W U D hUD).g 0 ≫
      (ordinaryAmbientIso p W U D hUD 0).hom) he

end TernaryPoly.SingularLocalCompactCapMV
