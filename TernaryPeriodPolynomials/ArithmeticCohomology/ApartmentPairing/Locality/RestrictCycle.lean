module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.SupportLemma
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.PDRep
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Embeddings

@[expose] public section


/-!
# Lemma 3.3, G3: a cycle carried over an open set has a dual supported inside it

`dual_of_carried`: if a degree-three coinvariant cycle `z` of the covering `p : E ⟶ B` is the image of a
chain of the restricted covering over an open set `D` of the base (`coinvariantSpaceMap_open_injective`
shows that the space map of the restriction is injective, so the restricted chain is again a cycle), then
its Poincaré dual in compactly supported cohomology has a representative supported in a compact subset of
`D` (the support lemma `dual_supported_in_open`), and the cap with the fundamental class recovers the
class of `z`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly TernaryPoly.RationalManifoldCompact
  TernaryPoly.SingularLocalSupport TernaryPoly.SingularLocalCompactCap
  TernaryPoly.SingularLocalCompactDuality TernaryPoly.RationalLocalOrientation
  TernaryPoly.SingularLocalCoefficient TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap.Descent TernaryPoly.SingularLocalCap
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.CoveringSingularOrbits
  TernaryPoly.FreeActionLinearization TernaryPoly.EquivariantSingularResolution
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

section Restrict

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [SecondCountableTopology B] [ChartedSpace H B]
  (e : H ≃ₜ EuclideanSpace ℝ (Fin (3+2))) (o : Orientation (3+2) B)
  (D : Opens B) [ChartedSpace H D]

omit [T2Space B] [SecondCountableTopology B] [ChartedSpace H B] [ChartedSpace H D] in
theorem coinvariantSpaceMap_open_injective (n : ℕ) :
    Function.Injective ((coinvariantSpaceMap (sInclusion (p ⁻¹' (D : Set B)))
      (fun _ _ => rfl) V).f n) := by
  let _ : IsCancelSMul G E := hp.out.isCancelSMul
  let _ : IsCancelSMul G (TopCat.of (p ⁻¹' (D : Set B))) :=
    (restrictedQuotientCovering p (D : Set B)).isCancelSMul
  have hp' : IsQuotientCoveringMap (restrictedProjection p (D : Set B)) G :=
      restrictedQuotientCovering p (D : Set B)
  have key : ∀ n, Function.Injective ((localSpaceMap (sInclusion (p ⁻¹' (D : Set B))) (fun _ _ => rfl) V
        (restrictedProjection p (D : Set B)) p hp' hp.out).f n) := fun n =>
    localSpaceMap_injective (restrictedProjection p (D : Set B)) p
      (sInclusion (p ⁻¹' (D : Set B))) (sInclusion (D : Set B)) rfl hp' hp.out (fun _ _ => rfl) V
      Subtype.val_injective n
  have h1 : ∀ (n : ℕ) (x : (coinvariantChains G (TopCat.of (p ⁻¹' (D : Set B))) V).X n),
      (degreeEquiv p hp.out V n).symm ((localSpaceMap (sInclusion (p ⁻¹' (D : Set B))) (fun _ _ => rfl) V
        (restrictedProjection p (D : Set B)) p hp' hp.out).f n
          (degreeEquiv (restrictedProjection p (D : Set B)) hp' V n x)) =
      (coinvariantSpaceMap (sInclusion (p ⁻¹' (D : Set B))) (fun _ _ => rfl) V).f n x := by
    intro n x
    have := localSpaceMap_degreeEquiv (restrictedProjection p (D : Set B)) p
      (sInclusion (p ⁻¹' (D : Set B))) hp' hp.out (fun _ _ => rfl) V n
      (degreeEquiv (restrictedProjection p (D : Set B)) hp' V n x)
    rw [LinearEquiv.symm_apply_apply] at this
    exact this
  intro x y hxy
  refine (degreeEquiv (restrictedProjection p (D : Set B)) hp' V n).injective (key n ?_)
  refine (degreeEquiv p hp.out V n).symm.injective ?_
  rw [h1 n x, h1 n y]
  exact hxy

/-- **A cycle carried over an open set has a dual supported in a compact inside it.** -/
theorem dual_of_carried (z : (coinvariantChains G E V).X 3)
    (hz : (coinvariantChains G E V).d 3 2 z = 0)
    (hzD : z ∈ LinearMap.range ((coinvariantSpaceMap (sInclusion (p ⁻¹' (D : Set B)))
      (fun _ _ => rfl) V).f 3).hom) :
    ∃ (K : Compacts B) (_ : (K : Set B) ⊆ D)
      (y : (supportCochains p V (K : Set B)).homology 2),
      letI : IsCancelSMul G E := hp.out.isCancelSMul
      compactCapMap p V 3 e o 2 3 rfl (compactClassMap p V K 2 y) =
        chainClass (localChains p hp.out V) 3
          (⟨degreeEquiv p hp.out V 3 z, degreeEquiv_cycle p V z hz⟩ :
            Cycles ((localChains p hp.out V).sc' (3+1) 3 (3-1))) := by
  let _ : IsCancelSMul G E := hp.out.isCancelSMul
  let _ : IsCancelSMul G (TopCat.of (p ⁻¹' (D : Set B))) :=
    (restrictedQuotientCovering p (D : Set B)).isCancelSMul
  have hp' : IsQuotientCoveringMap (restrictedProjection p (D : Set B)) G :=
    restrictedQuotientCovering p (D : Set B)
  have _ : Fact (IsQuotientCoveringMap (restrictedProjection p (D : Set B)) G) := ⟨hp'⟩
  obtain ⟨z', hz'⟩ := hzD
  have hd' : (coinvariantChains G (TopCat.of (p ⁻¹' (D : Set B))) V).d 3 2 z' = 0 := by
    apply coinvariantSpaceMap_open_injective p V D 2
    have hcomm := ConcreteCategory.congr_hom
      ((coinvariantSpaceMap (sInclusion (p ⁻¹' (D : Set B))) (fun _ _ => rfl) V).comm 3 2) z'
    have hcomm' : ((coinvariantSpaceMap (sInclusion (p ⁻¹' (D : Set B))) (fun _ _ => rfl) V).f 2)
        ((coinvariantChains G (TopCat.of (p ⁻¹' (D : Set B))) V).d 3 2 z') =
        (coinvariantChains G E V).d 3 2 (((coinvariantSpaceMap (sInclusion (p ⁻¹' (D : Set B)))
          (fun _ _ => rfl) V).f 3) z') := hcomm.symm
    rw [hcomm', hz', hz, map_zero]
  let cyc' : Cycles ((localChains (restrictedProjection p (D : Set B)) hp' V).sc' (3+1) 3 (3-1)) :=
    ⟨degreeEquiv (restrictedProjection p (D : Set B)) hp' V 3 z',
      degreeEquiv_cycle (restrictedProjection p (D : Set B)) V z' hd'⟩
  obtain ⟨K, hK, y, hy⟩ := dual_supported_in_open p V 3 e o D 2 3 rfl
    (chainClass (localChains (restrictedProjection p (D : Set B)) hp' V) 3 cyc')
  refine ⟨K, hK, y, hy.trans ?_⟩
  refine TernaryPoly.SingularLocalCompactCap.Algebra.chainClass_natural
    (openLocalChainMap p V (D : Set B)) 3 cyc' _ ?_
  have := localSpaceMap_degreeEquiv (restrictedProjection p (D : Set B)) p
    (sInclusion (p ⁻¹' (D : Set B))) hp' hp.out (fun _ _ => rfl) V 3
    (degreeEquiv (restrictedProjection p (D : Set B)) hp' V 3 z')
  rw [LinearEquiv.symm_apply_apply, hz'] at this
  exact ((LinearEquiv.symm_apply_eq _).mp this).symm

end Restrict

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
