module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.PointTransport

@[expose] public section


/-!
# The point class of a fundamental representative

A chain `c` of a manifold `B` representing the fundamental class over a compact support `K` has local class at each point `b ∈ K`
the orientation generator at `b`.

Formalized by Claude Sonnet 5.5.
-/

open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory CategoryTheory.Limits HomologicalComplex TopologicalSpace
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.RationalManifoldCompact
  TernaryPoly.RationalLocalChartHomology TernaryPoly.RationalRelativeExcision TernaryPoly.RationalLocalMap
  TernaryPoly.RationalSingularAugmentation TernaryPoly.RationalLocalOrientation
  TernaryPoly.SingularLocalCompactCap TernaryPoly.SingularLocalCompactDuality
open TernaryPoly.SingularLocalCap.Descent

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

theorem fundRep_pointClass {B : TopCat.{0}} [T2Space B] {H : Type} [TopologicalSpace H] [ChartedSpace H B]
    (e : H ≃ₜ EuclideanSpace ℝ (Fin (3 + 2))) (o : Orientation (3 + 2) B)
    (K : Compacts B) (c : singularChainGroup ℚ B (2 + 3)) (hc : IsFundRep e o K c)
    (b : B) (hb : b ∈ (K : Set B))
    (h0 : (singularBoundary ℚ B 4).hom c ∈ subChainSubmodule ℚ B ({b}ᶜ : Set B) 4) :
    rcls (X := B) ({b}ᶜ : Set B) 4 c h0 = o.generator b := by
  obtain ⟨hcyc, hcls⟩ := hc
  have hK : (singularBoundary ℚ B 4).hom c ∈ subChainSubmodule ℚ B ((K : Set B)ᶜ) 4 := by
    have hd := ConcreteCategory.congr_hom
      ((cokernel.π (RationalRelativeSingular.inclusion ((K : Set B)ᶜ))).comm (4 + 1) 4) c
    exact (rel_proj_eq_zero_iff _ 4 _).mp (hd.symm.trans hcyc)
  have h1 := compactFundamentalClass_at_point 3 e o (K : Set B) K.isCompact b hb
  have hcap : capFundamentalClass 3 e o K 2 3 rfl = compactFundamentalClass 3 e o (K : Set B) K.isCompact := rfl
  have hmaps : Set.MapsTo (𝟙 B : B ⟶ B).hom ((K : Set B)ᶜ) ({b}ᶜ : Set B) := by
    intro z hz hzb
    change z = b at hzb
    subst hzb
    exact hz hb
  have hid : (singularChainMap ℚ (𝟙 B) (4 + 1)).hom c = c :=
    congrArg (fun F => F.hom c) (singularChainMap_id ℚ _ _)
  have hidm : (singularBoundary ℚ B 4).hom ((singularChainMap ℚ (𝟙 B) (4 + 1)).hom c) ∈
      subChainSubmodule ℚ B ({b}ᶜ : Set B) 4 := by
    rw [hid]; exact h0
  have h2 := rcls_map (X := B) (Y := B) (𝟙 B) ((K : Set B)ᶜ) ({b}ᶜ : Set B) hmaps 4 c hK hidm
  have h3 : rcls (X := B) ({b}ᶜ : Set B) 4 ((singularChainMap ℚ (𝟙 B) (4 + 1)).hom c) hidm =
      rcls (X := B) ({b}ᶜ : Set B) 4 c h0 :=
    rcls_congr _ _ _ _ hid _ _
  rw [← h3, ← h2]
  have h4 : rcls (X := B) ((K : Set B)ᶜ) 4 c hK = compactFundamentalClass 3 e o (K : Set B) K.isCompact := by
    rw [← hcap]
    exact hcls
  rw [h4]
  exact h1

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
