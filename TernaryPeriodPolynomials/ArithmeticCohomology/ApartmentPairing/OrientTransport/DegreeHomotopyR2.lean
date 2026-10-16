module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.DegreeHomotopy
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.ThomR2

@[expose] public section


/-!
# Homotopy invariance of the planar local degree

`degR2_homotopy`: the dimension-two analogue of `Locality.degR3_homotopy` (a mechanical dimension shift of that file): two
maps `f, g : X ⟶ ℝ²` joined by a homotopy keeping a set `A` away from the origin have the same local degree on a 2-chain of
`X` whose boundary is subordinate to `A`.  It is used to compare Thom cochains of different radii.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.RationalRelativeSingular
  TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalSingularAugmentation
  TernaryPoly.ContractibleSingularHomology TernaryPoly.RationalSphere SphereOddDegree
  SphereOddDegree.AffineBarycentricSubdivision

theorem next_two' : (ComplexShape.down ℕ).next 2 = 1 :=
  (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 2 1 from rfl)

theorem homologyMap_homologyπ_cyclesMk2 {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L)
    (x : (forget₂ (ModuleCat.{0} ℚ) Ab).obj (K.X 2))
    (hx : (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.d 2 1) x = 0)
    (hφx : (forget₂ (ModuleCat.{0} ℚ) Ab).map (L.d 2 1)
      ((forget₂ (ModuleCat.{0} ℚ) Ab).map (φ.f 2) x) = 0) :
    (forget₂ (ModuleCat.{0} ℚ) Ab).map (homologyMap φ 2)
        ((forget₂ (ModuleCat.{0} ℚ) Ab).map (K.homologyπ 2) (K.cyclesMk x 1 next_two' hx)) =
      (forget₂ (ModuleCat.{0} ℚ) Ab).map (L.homologyπ 2)
        (L.cyclesMk ((forget₂ (ModuleCat.{0} ℚ) Ab).map (φ.f 2) x) 1 next_two' hφx) := by
  have inj : Function.Injective ((forget₂ (ModuleCat.{0} ℚ) Ab).map (L.iCycles 2)) :=
    (Preadditive.mono_iff_injective (L.iCycles 2)).1 inferInstance
  have hc : (forget₂ (ModuleCat.{0} ℚ) Ab).map (cyclesMap φ 2) (K.cyclesMk x 1 next_two' hx) =
      L.cyclesMk ((forget₂ (ModuleCat.{0} ℚ) Ab).map (φ.f 2) x) 1 next_two' hφx := by
    apply inj
    rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.forget₂_comp_apply, HomologicalComplex.i_cyclesMk,
      HomologicalComplex.i_cyclesMk]
  rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.forget₂_comp_apply, hc]

/-- **Homotopy invariance of the planar local degree.**  The dimension-two analogue of `Locality.degR3_homotopy`: two maps
`f, g : X ⟶ ℝ²` joined by a homotopy that keeps `A` away from the origin give the same local degree on a 2-chain whose
boundary is subordinate to `A`. -/
theorem degR2_homotopy {X : TopCat.{0}} (f g : X ⟶ TopCat.of R2)
    (H : ContinuousMap.Homotopy f.hom g.hom) (A : Set X)
    (hH : ∀ t x, x ∈ A → H (t, x) ∈ Punctured 2)
    (c : singularChainGroup ℚ X 2)
    (hc : (singularBoundary ℚ X 1).hom c ∈ subChainSubmodule ℚ X A 1) :
    ∃ (hf : ((localChains 2).d 2 1).hom ((locR2.f 2).hom ((singularChainMap ℚ f 2).hom c)) = 0)
      (hg : ((localChains 2).d 2 1).hom ((locR2.f 2).hom ((singularChainMap ℚ g 2).hom c)) = 0),
      degR2 ((singularChainMap ℚ f 2).hom c) hf = degR2 ((singularChainMap ℚ g 2).hom c) hg := by
  have hf0 : Set.MapsTo f.hom A (Punctured 2) := fun x hx => by
    have := hH 0 x hx
    rwa [H.apply_zero] at this
  have hg0 : Set.MapsTo g.hom A (Punctured 2) := fun x hx => by
    have := hH 1 x hx
    rwa [H.apply_one] at this
  -- the relative cycle of `c`
  have hcA : ((relativeChains A).d 2 1).hom ((cokernel.π (inclusion A)).f 2 |>.hom c) = 0 := by
    obtain ⟨y, hy⟩ := (subChainCorestrict_bijective (R := ℚ) A 1).2 ⟨_, hc⟩
    have hy' : (singularChainMap ℚ (sInclusion A) 1).hom y = (singularBoundary ℚ X 1).hom c :=
      congrArg Subtype.val hy
    have hcomm := ConcreteCategory.congr_hom ((cokernel.π (inclusion A)).comm 2 1) c
    refine hcomm.trans ?_
    have hz := (TernaryPoly.SingularLocalCap.RelativeAlgebra.projection_zero_iff (inclusion A) 1
      (((chains X).d 2 1).hom c)).mpr ⟨y, hy'⟩
    exact hz
  have key : ∀ (F : X ⟶ TopCat.of R2) (hF0 : Set.MapsTo F.hom A (Punctured 2)),
      ∃ hF : ((localChains 2).d 2 1).hom ((locR2.f 2).hom ((singularChainMap ℚ F 2).hom c)) = 0,
        degR2 ((singularChainMap ℚ F 2).hom c) hF =
          (localTopIso 0).hom.hom ((homologyMap (relativeMap F.hom A (Punctured 2) hF0) 2).hom
            ((relativeChains A).homologyπ 2
              ((relativeChains A).cyclesMk ((cokernel.π (inclusion A)).f 2 |>.hom c) 1 next_two' hcA))) := by
    intro F hF0
    have hπ : cokernel.π (inclusion A) ≫ relativeMap F.hom A (Punctured 2) hF0 =
        chainMap F.hom ≫ cokernel.π (inclusion (Punctured 2)) := by
      unfold relativeMap
      exact cokernel.π_desc _ _ _
    have hπ2 : (relativeMap F.hom A (Punctured 2) hF0).f 2 ((cokernel.π (inclusion A)).f 2 |>.hom c) =
        (locR2.f 2).hom ((singularChainMap ℚ F 2).hom c) :=
      ConcreteCategory.congr_hom (congrArg (fun G => G.f 2) hπ) c
    have hφx : ((localChains 2).d 2 1).hom ((relativeMap F.hom A (Punctured 2) hF0).f 2 |>.hom
        ((cokernel.π (inclusion A)).f 2 |>.hom c)) = 0 := by
      have hcm := ConcreteCategory.congr_hom ((relativeMap F.hom A (Punctured 2) hF0).comm 2 1)
        ((cokernel.π (inclusion A)).f 2 |>.hom c)
      refine hcm.trans ?_
      change ((relativeMap F.hom A (Punctured 2) hF0).f 1).hom
        (((relativeChains A).d 2 1).hom ((cokernel.π (inclusion A)).f 2 |>.hom c)) = 0
      rw [hcA, map_zero]
    have hF : ((localChains 2).d 2 1).hom ((locR2.f 2).hom ((singularChainMap ℚ F 2).hom c)) = 0 := by
      rw [← hπ2]; exact hφx
    refine ⟨hF, ?_⟩
    unfold degR2
    congr 1
    have hn := homologyMap_homologyπ_cyclesMk2 (relativeMap F.hom A (Punctured 2) hF0)
      ((cokernel.π (inclusion A)).f 2 |>.hom c) hcA hφx
    have hcy := thomCyclesMk_inj (localChains 2)
      ((locR2.f 2).hom ((singularChainMap ℚ F 2).hom c))
      ((relativeMap F.hom A (Punctured 2) hF0).f 2 |>.hom ((cokernel.π (inclusion A)).f 2 |>.hom c))
      1 next_two' hF hφx hπ2.symm
    rw [hcy]
    exact hn.symm
  obtain ⟨hf, hfe⟩ := key f hf0
  obtain ⟨hg, hge⟩ := key g hg0
  refine ⟨hf, hg, ?_⟩
  rw [hfe, hge]
  have hmap : homologyMap (relativeMap f.hom A (Punctured 2) hf0) 2 =
      homologyMap (relativeMap g.hom A (Punctured 2) hg0) 2 :=
    relativeHomologyMap_eq_of_homotopy f.hom g.hom A (Punctured 2) hf0 hg0 H hH 1 (by norm_num)
  rw [hmap]


end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
