module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Geometric.PosOrientation5
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.ChartChange

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
# Chart comparison and transported positive cell for the geometric orientation

Formalized by Claude Sonnet 5.5.

Paper: "we orient the flat and the averaged standard top-cell generator so that their local
intersection number is `+1`".  Closes the two comparison obligations:

* **Chart comparison** (`stairClassSpace_at`, `stairClassSpace_quotient`, `stairClassSpace_at_identity`): the staircase cell is a
  chain of `ℝ⁵` in the product chart `psi` (unipotent coordinates and log-pivots, through `ldlHomeomorph`).  The library orients
  the symmetric space through the global chart `spaceHomeomorph`; the two charts differ by the linear map `Lgl` of determinant
  `1/4 > 0` (`OrientTransport.localGenerator_eq_psiGenerator`).  Hence the staircase cell pushed into `Space` by `psi⁻¹`
  (`stairClassSpace`) restricts at every `S` in its support `NsetSpace` to `d₅` times the library's local generator at `S`, and its
  image under the covering projection to `d₅` times the quotient generator, the generator of `interiorOrientationGeo`.
* **Transported positive cell** (`stairClassTrans_at`): translations of `ℝ⁵` (isotopic to the identity) preserve the local
  generator (`trans_generator`), so the translate of the positive cell restricts at `y + v` to `posOrientation5.generator (y + v)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Geometric

theorem stair_pushed_at (S : Space) (hS : psi S ∈ (Nset : Set (EuclideanSpace ℝ (Fin (3 + 2))))) :
    (chartIso psi S).inv
        (homologyMap (supportPointMap (Nset : Set (EuclideanSpace ℝ (Fin (3 + 2)))) (psi S) hS) (3 + 2)
          (relCls stair (relCls_mem_of_sup stair_boundary_mem))) =
      d5 • SymmetricSpaceLocalOrientation.localGenerator S := by
  rw [stair_generator_at (psi S) hS, localGenerator_eq_psiGenerator]
  change (chartIso psi S).inv (d5 • localGenerator 3 (psi S)) = d5 • (chartIso psi S).inv (localGenerator 3 (psi S))
  exact map_smul _ _ _

open TernaryPoly.RationalRelativeSingular in
/-- The compact neighbourhood of the identity point of the symmetric space cut out by the staircase support `Nset` in the
product chart `psi`. -/
def NsetSpace : Set Space := psi ⁻¹' (Nset : Set (EuclideanSpace ℝ (Fin (3 + 2))))

open TernaryPoly.RationalRelativeSingular in
/-- **The staircase cell pushed into the symmetric space** by the product chart: the relative class in
`H₅(Space, Space ∖ NsetSpace)` that `psi` carries to the class of `stair`. -/
def stairClassSpace : (relativeChains ((NsetSpace : Set Space)ᶜ)).homology (3 + 2) :=
  ((homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) (3 + 2)).mapIso
    (relativeHomeomorphIso psi ((NsetSpace : Set Space)ᶜ) ((Nset : Set (EuclideanSpace ℝ (Fin (3 + 2))))ᶜ)
      (fun _ => Iff.rfl))).inv
    (relCls stair (relCls_mem_of_sup stair_boundary_mem))

open TernaryPoly.RationalRelativeSingular in
/-- **Chart comparison for the pushed staircase cell**: the restriction at any `S ∈ NsetSpace` of the staircase cell pushed
into the symmetric space by the product chart `psi` is `d₅` times the library's orientation generator at `S`.  (Chart
comparison `ldlHomeomorph` vs `spaceHomeomorph` is `OrientTransport.localGenerator_eq_psiGenerator`: the two charts differ by
the positive-determinant linear map `Lgl`.) -/
theorem stairClassSpace_at (S : Space) (hS : S ∈ NsetSpace) :
    homologyMap (supportPointMap (NsetSpace : Set Space) S hS) (3 + 2) stairClassSpace =
      d5 • SymmetricSpaceLocalOrientation.localGenerator S := by
  have hpsi : Set.MapsTo (psi.toHomotopyEquiv.toFun : C(Space, EuclideanSpace ℝ (Fin 5)))
      ((NsetSpace : Set Space)ᶜ) ((Nset : Set (EuclideanSpace ℝ (Fin (3 + 2))))ᶜ) := fun _ hx => hx
  have hpsi' : Set.MapsTo (psi.toHomotopyEquiv.toFun : C(Space, EuclideanSpace ℝ (Fin 5)))
      ({S}ᶜ : Set Space) ({psi S}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) := by
    intro x hx hxs
    exact hx (psi.injective hxs)
  have hsq : relativeMap (psi.toHomotopyEquiv.toFun : C(Space, EuclideanSpace ℝ (Fin 5)))
        ((NsetSpace : Set Space)ᶜ) ((Nset : Set (EuclideanSpace ℝ (Fin (3 + 2))))ᶜ) hpsi ≫
      supportPointMap (Nset : Set (EuclideanSpace ℝ (Fin (3 + 2)))) (psi S) hS =
      supportPointMap (NsetSpace : Set Space) S hS ≫
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
      ((NsetSpace : Set Space)ᶜ) ((Nset : Set (EuclideanSpace ℝ (Fin (3 + 2))))ᶜ) hpsi) (3 + 2) stairClassSpace =
      relCls stair (relCls_mem_of_sup stair_boundary_mem) := by
    unfold stairClassSpace
    exact Iso.inv_hom_id_apply ((homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) (3 + 2)).mapIso
    (relativeHomeomorphIso psi ((NsetSpace : Set Space)ᶜ) ((Nset : Set (EuclideanSpace ℝ (Fin (3 + 2))))ᶜ)
      (fun _ => Iff.rfl))) _
  have h1 : (chartIso psi S).hom (homologyMap (supportPointMap (NsetSpace : Set Space) S hS) (3 + 2) stairClassSpace) =
      posOrientation5.generator (psi S) := by
    rw [hchart]
    have hsq' := congrArg (fun f => homologyMap f (3 + 2)) hsq
    simp only [homologyMap_comp] at hsq'
    have := ConcreteCategory.congr_hom hsq' stairClassSpace
    rw [← stair_generator_at (psi S) hS, ← hhom]
    exact this.symm
  apply (ModuleCat.mono_iff_injective (chartIso psi S).hom).mp inferInstance
  rw [h1, map_smul, localGenerator_eq_psiGenerator]
  change _ = d5 • (chartIso psi S).hom ((chartIso psi S).inv (localGenerator 3 (psi S)))
  rw [Iso.inv_hom_id_apply]
  rfl

open TernaryPoly.SymmetricSpaceQuotientOrientation TernaryPoly.RationalLocalMap
  TernaryPoly.RationalLocalChartHomology in
/-- **The pushed staircase cell represents the geometric orientation of the arithmetic quotient**: pushing the restriction of
`stairClassSpace` at `S` through the actual covering `projection` (local homeomorphism) gives `d₅` times the quotient
generator at `projection S`, i.e. the generator of `interiorOrientationGeo` (up to the literal interior homeomorphism). -/
theorem stairClassSpace_quotient (S : Space) (hS : S ∈ NsetSpace) :
    localHomeomorphMap projection projection_localHomeomorph S 5
        (homologyMap (supportPointMap (NsetSpace : Set Space) S hS) (3 + 2) stairClassSpace) =
      d5 • SymmetricSpaceQuotientOrientation.localGenerator (projection S) := by
  rw [stairClassSpace_at S hS, map_smul, localGenerator_projection]

/-- At the identity point `p0` of the symmetric space (`psi p0 = 0`), which lies in `NsetSpace`. -/
theorem p0_mem_NsetSpace : Locality.p0 ∈ NsetSpace := by
  change psi Locality.p0 ∈ (Nset : Set (EuclideanSpace ℝ (Fin (3 + 2))))
  rw [psi_p0]
  exact zero_mem_Nset

/-- **At the identity point the pushed positive staircase cell is `d₅` times the library's generator.** -/
theorem stairClassSpace_at_identity :
    homologyMap (supportPointMap (NsetSpace : Set Space) Locality.p0 p0_mem_NsetSpace) (3 + 2) stairClassSpace =
      d5 • SymmetricSpaceLocalOrientation.localGenerator Locality.p0 :=
  stairClassSpace_at _ _

section Translation

abbrev E5' := EuclideanSpace ℝ (Fin (3 + 2))

/-- Translation of `ℝ⁵` as a continuous self-map. -/
def transMap (v : E5') : C(E5', E5') := ⟨fun z => z + v, continuous_id.add continuous_const⟩

theorem transMap_injective (v : E5') : Function.Injective (transMap v) := fun _ _ h => add_right_cancel h

/-- The straight-line isotopy from the identity to a translation. -/
def transHomotopy (v : E5') : ContinuousMap.Homotopy (ContinuousMap.id E5') (transMap v) where
  toFun z := z.2 + (z.1 : ℝ) • v
  continuous_toFun := by fun_prop
  map_zero_left z := by simp
  map_one_left z := by simp [transMap]

/-- Translations preserve the local generator of `ℝ⁵`. -/
theorem trans_generator (v x : E5') :
    homologyMap (pointLocalMap (transMap v) (transMap_injective v) x) (3 + 2) (localGenerator 3 x) =
      localGenerator 3 (x + v) :=
  pointLocalMap_generator 3 (transMap v) (transMap_injective v) (transHomotopy v)
    (fun t a b h => by
      have h' : a + (t : ℝ) • v = b + (t : ℝ) • v := h
      exact add_right_cancel h') x

/-- The support of the translated staircase cell. -/
def NsetTrans (v : E5') : Set E5' := (fun z => z - v) ⁻¹' (Nset : Set E5')

open TernaryPoly.RationalRelativeSingular in
/-- **The positive staircase cell transported by a translation** of `ℝ⁵`. -/
def stairClassTrans (v : E5') : (relativeChains ((NsetTrans v)ᶜ)).homology (3 + 2) :=
  homologyMap (relativeMap (transMap v) ((Nset : Set E5')ᶜ) ((NsetTrans v)ᶜ)
    (fun z hz hz' => hz (by simpa [NsetTrans, transMap] using hz'))) (3 + 2)
    (relCls stair (relCls_mem_of_sup stair_boundary_mem))

open TernaryPoly.RationalRelativeSingular in
/-- **Transported positive-cell comparison**: the translated staircase cell restricts at the translated point `y + v` to the
geometric generator `posOrientation5.generator (y + v)`; so the positive cell represents the geometric orientation of `ℝ⁵` at
every point of the translated support, for every translation. -/
theorem stairClassTrans_at (v y : E5') (hy : y ∈ (Nset : Set E5')) :
    homologyMap (supportPointMap (NsetTrans v) (y + v) (by simpa [NsetTrans] using hy)) (3 + 2) (stairClassTrans v) =
      posOrientation5.generator (y + v) := by
  have hmaps : Set.MapsTo (transMap v) (((Nset : Set E5'))ᶜ) ((NsetTrans v)ᶜ) :=
    fun z hz hz' => hz (by simpa [NsetTrans, transMap] using hz')
  have hsq : relativeMap (transMap v) ((Nset : Set E5')ᶜ) ((NsetTrans v)ᶜ) hmaps ≫
      supportPointMap (NsetTrans v) (y + v) (by simpa [NsetTrans] using hy) =
      supportPointMap (Nset : Set E5') y hy ≫ pointLocalMap (transMap v) (transMap_injective v) y := by
    unfold supportPointMap pointLocalMap
    rw [relativeMap_comp]
    erw [relativeMap_comp]
    rfl
  have hsq' := congrArg (fun f => homologyMap f (3 + 2)) hsq
  simp only [homologyMap_comp] at hsq'
  have h1 := ConcreteCategory.congr_hom hsq' (relCls stair (relCls_mem_of_sup stair_boundary_mem))
  change _ = _ at h1
  unfold stairClassTrans
  refine h1.trans ?_
  erw [homologyMap_comp, ConcreteCategory.comp_apply]
  change (homologyMap (pointLocalMap (transMap v) (transMap_injective v) y)
    (3 + 2)).hom ((homologyMap (supportPointMap (Nset : Set E5') y hy) (3 + 2)).hom
      (relCls stair (relCls_mem_of_sup stair_boundary_mem))) = _
  rw [stair_generator_at y hy]
  change (homologyMap (pointLocalMap (transMap v) (transMap_injective v) y) (3 + 2)).hom
    (d5 • localGenerator 3 y) = d5 • localGenerator 3 (y + v)
  rw [map_smul]
  exact congrArg (d5 • ·) (trans_generator v y)

end Translation

end TernaryPeriodPolynomials.Argument.Lemma33.Geometric
