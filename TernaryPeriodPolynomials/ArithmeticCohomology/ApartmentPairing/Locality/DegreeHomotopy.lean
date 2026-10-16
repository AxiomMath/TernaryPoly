module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.ThomY
public import TernaryPeriodPolynomials.Topology.Rational.Relative.Homotopy

@[expose] public section


/-!
# Lemma 3.3, G3: the local degree is invariant under pair-preserving homotopy

`degR3_homotopy`: two maps `f, g : X ⟶ ℝ³` joined by a homotopy that keeps a set `A` away from the origin
give the same local degree on a 3-chain `c` of `X` whose boundary is subordinate to `A`.  This compares the
degree of the scaled projection `π/ρ'` used for the thin Thom cochain with the degree of `π` itself.
`homologyMap_homologyπ_cyclesMk` is the naturality of the cycle class construction.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.RationalRelativeSingular
  TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalSingularAugmentation
  TernaryPoly.ContractibleSingularHomology TernaryPoly.RationalSphere SphereOddDegree
  SphereOddDegree.AffineBarycentricSubdivision

theorem next_three' : (ComplexShape.down ℕ).next 3 = 2 :=
  (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 3 2 from rfl)

theorem homologyMap_homologyπ_cyclesMk {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L)
    (x : (forget₂ (ModuleCat.{0} ℚ) Ab).obj (K.X 3))
    (hx : (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.d 3 2) x = 0)
    (hφx : (forget₂ (ModuleCat.{0} ℚ) Ab).map (L.d 3 2)
      ((forget₂ (ModuleCat.{0} ℚ) Ab).map (φ.f 3) x) = 0) :
    (forget₂ (ModuleCat.{0} ℚ) Ab).map (homologyMap φ 3)
        ((forget₂ (ModuleCat.{0} ℚ) Ab).map (K.homologyπ 3) (K.cyclesMk x 2 next_three' hx)) =
      (forget₂ (ModuleCat.{0} ℚ) Ab).map (L.homologyπ 3)
        (L.cyclesMk ((forget₂ (ModuleCat.{0} ℚ) Ab).map (φ.f 3) x) 2 next_three' hφx) := by
  have inj : Function.Injective ((forget₂ (ModuleCat.{0} ℚ) Ab).map (L.iCycles 3)) :=
    (Preadditive.mono_iff_injective (L.iCycles 3)).1 inferInstance
  have hc : (forget₂ (ModuleCat.{0} ℚ) Ab).map (cyclesMap φ 3) (K.cyclesMk x 2 next_three' hx) =
      L.cyclesMk ((forget₂ (ModuleCat.{0} ℚ) Ab).map (φ.f 3) x) 2 next_three' hφx := by
    apply inj
    rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.forget₂_comp_apply, HomologicalComplex.i_cyclesMk,
      HomologicalComplex.i_cyclesMk]
  rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.forget₂_comp_apply, hc]

theorem degR3_homotopy {X : TopCat.{0}} (f g : X ⟶ TopCat.of R3)
    (H : ContinuousMap.Homotopy f.hom g.hom) (A : Set X)
    (hH : ∀ t x, x ∈ A → H (t, x) ∈ Punctured 3)
    (c : singularChainGroup ℚ X 3)
    (hc : (singularBoundary ℚ X 2).hom c ∈ subChainSubmodule ℚ X A 2) :
    ∃ (hf : ((localChains 3).d 3 2).hom ((locR3.f 3).hom ((singularChainMap ℚ f 3).hom c)) = 0)
      (hg : ((localChains 3).d 3 2).hom ((locR3.f 3).hom ((singularChainMap ℚ g 3).hom c)) = 0),
      degR3 ((singularChainMap ℚ f 3).hom c) hf = degR3 ((singularChainMap ℚ g 3).hom c) hg := by
  have hf0 : Set.MapsTo f.hom A (Punctured 3) := fun x hx => by
    have := hH 0 x hx
    rwa [H.apply_zero] at this
  have hg0 : Set.MapsTo g.hom A (Punctured 3) := fun x hx => by
    have := hH 1 x hx
    rwa [H.apply_one] at this
  -- the relative cycle of `c`
  have hcA : ((relativeChains A).d 3 2).hom ((cokernel.π (inclusion A)).f 3 |>.hom c) = 0 := by
    obtain ⟨y, hy⟩ := (subChainCorestrict_bijective (R := ℚ) A 2).2 ⟨_, hc⟩
    have hy' : (singularChainMap ℚ (sInclusion A) 2).hom y = (singularBoundary ℚ X 2).hom c :=
      congrArg Subtype.val hy
    have hcomm := ConcreteCategory.congr_hom ((cokernel.π (inclusion A)).comm 3 2) c
    refine hcomm.trans ?_
    have hz := (TernaryPoly.SingularLocalCap.RelativeAlgebra.projection_zero_iff (inclusion A) 2
      (((chains X).d 3 2).hom c)).mpr ⟨y, hy'⟩
    exact hz
  have key : ∀ (F : X ⟶ TopCat.of R3) (hF0 : Set.MapsTo F.hom A (Punctured 3)),
      ∃ hF : ((localChains 3).d 3 2).hom ((locR3.f 3).hom ((singularChainMap ℚ F 3).hom c)) = 0,
        degR3 ((singularChainMap ℚ F 3).hom c) hF =
          (localTopIso 1).hom.hom ((homologyMap (relativeMap F.hom A (Punctured 3) hF0) 3).hom
            ((relativeChains A).homologyπ 3
              ((relativeChains A).cyclesMk ((cokernel.π (inclusion A)).f 3 |>.hom c) 2 next_three' hcA))) := by
    intro F hF0
    have hπ : cokernel.π (inclusion A) ≫ relativeMap F.hom A (Punctured 3) hF0 =
        chainMap F.hom ≫ cokernel.π (inclusion (Punctured 3)) := by
      unfold relativeMap
      exact cokernel.π_desc _ _ _
    have hπ3 : (relativeMap F.hom A (Punctured 3) hF0).f 3 ((cokernel.π (inclusion A)).f 3 |>.hom c) =
        (locR3.f 3).hom ((singularChainMap ℚ F 3).hom c) :=
      ConcreteCategory.congr_hom (congrArg (fun G => G.f 3) hπ) c
    have hφx : ((localChains 3).d 3 2).hom ((relativeMap F.hom A (Punctured 3) hF0).f 3 |>.hom
        ((cokernel.π (inclusion A)).f 3 |>.hom c)) = 0 := by
      have hcm := ConcreteCategory.congr_hom ((relativeMap F.hom A (Punctured 3) hF0).comm 3 2)
        ((cokernel.π (inclusion A)).f 3 |>.hom c)
      refine hcm.trans ?_
      change ((relativeMap F.hom A (Punctured 3) hF0).f 2).hom
        (((relativeChains A).d 3 2).hom ((cokernel.π (inclusion A)).f 3 |>.hom c)) = 0
      rw [hcA, map_zero]
    have hF : ((localChains 3).d 3 2).hom ((locR3.f 3).hom ((singularChainMap ℚ F 3).hom c)) = 0 := by
      rw [← hπ3]; exact hφx
    refine ⟨hF, ?_⟩
    unfold degR3
    congr 1
    have hn := homologyMap_homologyπ_cyclesMk (relativeMap F.hom A (Punctured 3) hF0)
      ((cokernel.π (inclusion A)).f 3 |>.hom c) hcA hφx
    have hcy := thomCyclesMk_inj (localChains 3)
      ((locR3.f 3).hom ((singularChainMap ℚ F 3).hom c))
      ((relativeMap F.hom A (Punctured 3) hF0).f 3 |>.hom ((cokernel.π (inclusion A)).f 3 |>.hom c))
      2 next_three' hF hφx hπ3.symm
    rw [hcy]
    exact hn.symm
  obtain ⟨hf, hfe⟩ := key f hf0
  obtain ⟨hg, hge⟩ := key g hg0
  refine ⟨hf, hg, ?_⟩
  rw [hfe, hge]
  have hmap : homologyMap (relativeMap f.hom A (Punctured 3) hf0) 3 =
      homologyMap (relativeMap g.hom A (Punctured 3) hg0) 3 :=
    relativeHomologyMap_eq_of_homotopy f.hom g.hom A (Punctured 3) hf0 hg0 H hH 2 (by norm_num)
  rw [hmap]

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
