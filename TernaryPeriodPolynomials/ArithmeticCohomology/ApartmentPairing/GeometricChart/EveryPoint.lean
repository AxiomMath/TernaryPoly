module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Geometric.ChartCompare

@[expose] public section


open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.RationalManifoldCompact TernaryPoly.EuclideanCompactClasses
  TernaryPoly.RationalLocalOrientation TernaryPoly.EuclideanOrientationScalar
open TernaryPoly.SymmetricSpacePositive
open TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
open TernaryPeriodPolynomials.Argument.Lemma33.Geometric

/-!
# The positive reference cell, transported to every point of the symmetric space

Formalized by Claude Sonnet 5.5.

`Geometric/ChartCompare` compares the pushed staircase cell with the library's generator at the points of a neighbourhood
`NsetSpace` of the identity (`stairClassSpace_at`) and proves that translations of `R^5` carry the positive cell to the geometric
generator (`stairClassTrans_at`).  Here the two are combined: the translate of the positive cell by `v`, pushed into the symmetric
space by the product chart, restricts at every `S` of its support to `d₅` times the library's local generator at `S`
(`stairClassSpaceTrans_at`), and for every point `S` of the symmetric space there is such a cell supported around `S`
(`exists_positive_cell_at`): the positive reference cell transported to any point agrees with the library's consistent generator
up to the single global scale `d₅`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.GeometricChart

open TernaryPoly.RationalRelativeSingular

/-- The support, in the symmetric space, of the translate of the staircase cell by `v` (in the product chart). -/
def NsetSpaceTrans (v : E5') : Set Space := psi ⁻¹' (NsetTrans v)

/-- The translate of the positive staircase cell by `v`, pushed into the symmetric space by the product chart `psi`. -/
def stairClassSpaceTrans (v : E5') : (relativeChains ((NsetSpaceTrans v : Set Space)ᶜ)).homology (3 + 2) :=
  ((homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) (3 + 2)).mapIso
    (relativeHomeomorphIso psi ((NsetSpaceTrans v : Set Space)ᶜ) ((NsetTrans v)ᶜ)
      (fun _ => Iff.rfl))).inv (stairClassTrans v)

/-- The translated cell restricts at every point `z` of its support to the geometric generator. -/
theorem stairClassTrans_at' (v z : E5') (hz : z ∈ NsetTrans v) :
    homologyMap (supportPointMap (NsetTrans v) z hz) (3 + 2) (stairClassTrans v) =
      posOrientation5.generator z := by
  obtain ⟨y, rfl⟩ : ∃ y, z = y + v := ⟨z - v, by simp⟩
  have hy : y ∈ (Nset : Set E5') := by simpa [NsetTrans] using hz
  exact stairClassTrans_at v y hy

/-- **The transported positive cell is `d₅` times the library's local generator at every point of its support.** -/
theorem stairClassSpaceTrans_at (v : E5') (S : Space) (hS : S ∈ NsetSpaceTrans v) :
    homologyMap (supportPointMap (NsetSpaceTrans v : Set Space) S hS) (3 + 2) (stairClassSpaceTrans v) =
      d5 • SymmetricSpaceLocalOrientation.localGenerator S := by
  have hpsi : Set.MapsTo (psi.toHomotopyEquiv.toFun : C(Space, EuclideanSpace ℝ (Fin 5)))
      ((NsetSpaceTrans v : Set Space)ᶜ) ((NsetTrans v)ᶜ) := fun _ hx => hx
  have hpsi' : Set.MapsTo (psi.toHomotopyEquiv.toFun : C(Space, EuclideanSpace ℝ (Fin 5)))
      ({S}ᶜ : Set Space) ({psi S}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) := by
    intro x hx hxs
    exact hx (psi.injective hxs)
  have hS' : psi S ∈ NsetTrans v := hS
  have hsq : relativeMap (psi.toHomotopyEquiv.toFun : C(Space, EuclideanSpace ℝ (Fin 5)))
        ((NsetSpaceTrans v : Set Space)ᶜ) ((NsetTrans v)ᶜ) hpsi ≫
      supportPointMap (NsetTrans v) (psi S) hS' =
      supportPointMap (NsetSpaceTrans v : Set Space) S hS ≫
        relativeMap (psi.toHomotopyEquiv.toFun : C(Space, EuclideanSpace ℝ (Fin 5)))
          ({S}ᶜ : Set Space) ({psi S}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) hpsi' := by
    unfold supportPointMap
    rw [relativeMap_comp, relativeMap_comp]
    rfl
  have hchart : (chartIso psi S).hom = homologyMap (relativeMap
      (psi.toHomotopyEquiv.toFun : C(Space, EuclideanSpace ℝ (Fin 5)))
      ({S}ᶜ : Set Space) ({psi S}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) hpsi') (3 + 2) := by
    unfold chartIso
    simp only [Functor.mapIso_hom, relativeHomeomorphIso_hom]
    rfl
  have hhom : homologyMap (relativeMap (psi.toHomotopyEquiv.toFun : C(Space, EuclideanSpace ℝ (Fin 5)))
      ((NsetSpaceTrans v : Set Space)ᶜ) ((NsetTrans v)ᶜ) hpsi) (3 + 2) (stairClassSpaceTrans v) =
      stairClassTrans v := by
    unfold stairClassSpaceTrans
    exact Iso.inv_hom_id_apply ((homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) (3 + 2)).mapIso
      (relativeHomeomorphIso psi ((NsetSpaceTrans v : Set Space)ᶜ) ((NsetTrans v)ᶜ) (fun _ => Iff.rfl))) _
  have h1 : (chartIso psi S).hom (homologyMap (supportPointMap (NsetSpaceTrans v : Set Space) S hS) (3 + 2)
      (stairClassSpaceTrans v)) = posOrientation5.generator (psi S) := by
    rw [hchart]
    have hsq' := congrArg (fun f => homologyMap f (3 + 2)) hsq
    simp only [homologyMap_comp] at hsq'
    have := ConcreteCategory.congr_hom hsq' (stairClassSpaceTrans v)
    have hT := stairClassTrans_at' v (psi S) hS'
    rw [← hhom] at hT
    exact this.symm.trans hT
  apply (ModuleCat.mono_iff_injective (chartIso psi S).hom).mp inferInstance
  rw [h1, map_smul, localGenerator_eq_psiGenerator]
  change _ = d5 • (chartIso psi S).hom ((chartIso psi S).inv (localGenerator 3 (psi S)))
  rw [Iso.inv_hom_id_apply]
  rfl

/-- **For every point `S` of the symmetric space there is a pushed positive cell around `S` whose restriction at `S` is `d₅` times
the library's local generator at `S`** (translate by `v = psi S`; `psi S - v = 0` lies in `Nset`). -/
theorem exists_positive_cell_at (S : Space) :
    ∃ (K : Set Space) (hS : S ∈ K) (c : (relativeChains ((K : Set Space)ᶜ)).homology (3 + 2)),
      homologyMap (supportPointMap K S hS) (3 + 2) c = d5 • SymmetricSpaceLocalOrientation.localGenerator S := by
  have hS : S ∈ NsetSpaceTrans (psi S) := by
    change psi S ∈ NsetTrans (psi S)
    simpa [NsetTrans] using zero_mem_Nset
  exact ⟨_, hS, stairClassSpaceTrans (psi S), stairClassSpaceTrans_at (psi S) S hS⟩

open TernaryPoly.SymmetricSpaceQuotientOrientation TernaryPoly.RationalLocalMap
  TernaryPoly.RationalLocalChartHomology in
/-- The same in the arithmetic quotient: the image of the transported cell under the covering `projection` is `d₅` times the
quotient generator, i.e. the generator of `interiorOrientationGeo`. -/
theorem stairClassSpaceTrans_quotient (v : E5') (S : Space) (hS : S ∈ NsetSpaceTrans v) :
    localHomeomorphMap projection projection_localHomeomorph S 5
        (homologyMap (supportPointMap (NsetSpaceTrans v : Set Space) S hS) (3 + 2) (stairClassSpaceTrans v)) =
      d5 • SymmetricSpaceQuotientOrientation.localGenerator (projection S) := by
  rw [stairClassSpaceTrans_at v S hS, map_smul, localGenerator_projection]

end TernaryPeriodPolynomials.Argument.Lemma33.GeometricChart
