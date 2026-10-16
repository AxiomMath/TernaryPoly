module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Orient.Nonvanish
public import TernaryPeriodPolynomials.Topology.Euclidean.OrientationScalar

@[expose] public section


/-!
# Calibration of the local class `lamPos` against Euclidean orientations

For every homological orientation `o` of `ℝ³` in the sense of `TernaryPoly.EuclideanOrientationScalar`
and every relative 3-cycle `c` of `(ℝ³, ℝ³ ∖ 0)`, the class of `c` is the local degree `degRel c`
divided by `orientationScalar 1 o` times the generator `o.generator 0`
(`relCls_eq_ratio_smul`).  Both constants are read in the same coordinate `localTopIso 1`, so the
non-canonical choice inside `zeroReducedHomologyIso` cancels in the ratio.  In particular a
positively oriented tetrahedron has class `(lamPos / orientationScalar 1 o) • o.generator 0` and the
standard top cell has class `-(lamPos / orientationScalar 1 o) • o.generator 0`
(`tetra_class_eq_ratio`, `topCell_class_eq_ratio`).  `translate_zero_hom` records that the translation
isomorphism of local homology at the origin is the identity.

The library's `euclideanOrientation` has `orientationScalar = 1` by definition, so for it the ratio is
`lamPos` itself (`ratio_euclidean`), which is not canonically `±1` (it depends on the choice inside
`zeroReducedHomologyIso`).  The canonical *geometric* orientation is `posOrientation` (the Euclidean
one rescaled by `lamPos`): `ratio_pos : lamPos / orientationScalar 1 posOrientation = 1`, and
`tetra_generator_at` shows that a positively oriented tetrahedron around any point `y` has class
exactly `posOrientation.generator y`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical
open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.RationalRelativeSingular
  TernaryPoly.RationalSingularAugmentation TernaryPoly.ContractibleSingularHomology
  TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalSphere TernaryPoly.RationalLocalOrientation
  TernaryPoly.EuclideanOrientationScalar

namespace TernaryPeriodPolynomials.Argument.Lemma33.Orient

theorem translate_zero_hom (k : ℕ) :
    (translateLocalHomologyIso 3 0 k).hom = 𝟙 _ := by
  unfold translateLocalHomologyIso translateLocalIso
  rw [Functor.mapIso_hom, relativeHomeomorphIso_hom]
  have hf : (Homeomorph.subRight (0 : E3)).toHomotopyEquiv.toFun = ContinuousMap.id E3 := by
    ext x; simp
  have key : ∀ (g : C(E3, E3)) (hg : g = ContinuousMap.id E3) (h : Set.MapsTo g ({0}ᶜ : Set E3) ({0}ᶜ : Set E3)),
      relativeMap g ({0}ᶜ : Set E3) ({0}ᶜ : Set E3) h = 𝟙 _ := by
    intro g hg h
    subst hg
    exact relativeMap_id _
  exact (congrArg (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).map (key _ hf _)).trans
    (CategoryTheory.Functor.map_id _ _)


/-- The scalar of an orientation, read in the coordinate `localTopIso 1` at the origin. -/
theorem orientationScalar_eq (o : Orientation (1 + 2) (EuclideanSpace ℝ (Fin (1 + 2)))) :
    (localTopIso 1).hom.hom (o.generator 0) = orientationScalar 1 o := by
  have e : (translateLocalHomologyIso 3 0 3).hom ≫ (localTopIso 1).hom = (localTopIso 1).hom := by
    rw [translate_zero_hom, Category.id_comp]
  exact congrArg (fun f => f.hom (o.generator 0)) e.symm

/-- **Orientation transport at the origin**: the class of any relative 3-cycle of `(ℝ³, ℝ³∖0)` is its
local degree divided by the scalar of the orientation `o`, times the generator `o.generator 0`. -/
theorem relCls_eq_ratio_smul (o : Orientation (1 + 2) (EuclideanSpace ℝ (Fin (1 + 2))))
    (c : AbF.obj ((chains E3).X 3)) (hc : RelCycle (Punctured 3) c) :
    (relCls (Punctured 3) c hc : (relativeChains (Punctured 3)).homology 3) =
      (degRel c hc / orientationScalar 1 o) • (o.generator 0 : (relativeChains (Punctured 3)).homology 3) := by
  have hinj : Function.Injective (localTopIso 1).hom.hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hinj
  rw [map_smul, orientationScalar_eq, smul_eq_mul]
  have hne : orientationScalar 1 o ≠ 0 := orientationScalar_ne_zero 1 o
  rw [div_mul_cancel₀ _ hne]
  rfl

/-- A positively oriented tetrahedron around the origin has class `(lamPos / orientationScalar) • generator`. -/
theorem tetra_class_eq_ratio (o : Orientation (1 + 2) (EuclideanSpace ℝ (Fin (1 + 2))))
    (w : Fin (3 + 1) → E3) (τ : Fin (3 + 1) → ℝ) (hτ : ∀ k, 0 < τ k) (hrel : ∑ k, τ k • w k = 0)
    (hdet : 0 < edgeDet w) :
    (relCls (Punctured 3) (sing (TopCat.of E3) (simpOf (affEMap w)))
        (simplex_relCycle (affEMap w) (facesAvoid_of_rel w τ hτ hrel hdet)) :
        (relativeChains (Punctured 3)).homology 3) =
      (lamPos / orientationScalar 1 o) • (o.generator 0 : (relativeChains (Punctured 3)).homology 3) := by
  have h := relCls_eq_ratio_smul o (sing (TopCat.of E3) (simpOf (affEMap w)))
    (simplex_relCycle (affEMap w) (facesAvoid_of_rel w τ hτ hrel hdet))
  rw [h]
  have h2 : degRel (sing (TopCat.of E3) (simpOf (affEMap w)))
      (simplex_relCycle (affEMap w) (facesAvoid_of_rel w τ hτ hrel hdet)) = lamPos :=
    degAff_universal w (facesAvoid_of_rel w τ hτ hrel hdet) τ hτ hrel hdet
  rw [h2]

/-- The standard top cell has class `-(lamPos / orientationScalar) • generator`. -/
theorem topCell_class_eq_ratio (o : Orientation (1 + 2) (EuclideanSpace ℝ (Fin (1 + 2)))) :
    (relCls (Punctured 3)
        (AbF.map ((chainMap TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree.piR3).f 3)
          (TernaryPeriodPolynomials.Argument.Lemma33.Retract.cellAtSpace 3
            TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry.T0))
        TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree.cycle_T0 :
        (relativeChains (Punctured 3)).homology 3) =
      (-(lamPos / orientationScalar 1 o)) •
        (o.generator 0 : (relativeChains (Punctured 3)).homology 3) := by
  have h := relCls_eq_ratio_smul o
    (AbF.map ((chainMap TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree.piR3).f 3)
      (TernaryPeriodPolynomials.Argument.Lemma33.Retract.cellAtSpace 3
        TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry.T0))
    TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree.cycle_T0
  rw [h]
  have : degRel (AbF.map ((chainMap TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree.piR3).f 3)
      (TernaryPeriodPolynomials.Argument.Lemma33.Retract.cellAtSpace 3
        TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry.T0))
      TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree.cycle_T0 = -lamPos := by
    rw [← dT0_eq_neg_lamPos]; rfl
  rw [this, neg_div]


/-! ### The standard orientation of the library and the positive geometric orientation -/

theorem orientationScalar_euclidean : orientationScalar 1 (euclideanOrientation 1) = 1 := by
  unfold orientationScalar
  change (localTopAtIso 1 0).hom ((localTopAtIso 1 0).inv (1 : ℚ)) = 1
  exact congrArg (fun f => f.hom (1 : ℚ)) (Iso.inv_hom_id (localTopAtIso 1 0))

/-- For the library's `euclideanOrientation` the ratio is `lamPos` itself: it is not `±1`, because both
`lamPos` and the local generator are defined through the non-canonical `zeroReducedHomologyIso`. -/
theorem ratio_euclidean : lamPos / orientationScalar 1 (euclideanOrientation 1) = lamPos := by
  rw [orientationScalar_euclidean, div_one]

/-- **The positive geometric orientation of `ℝ³`**: the Euclidean orientation rescaled by `lamPos`, so
that its generator at `0` is the class of a positively oriented tetrahedron around `0`. -/
def posOrientation : Orientation (1 + 2) (EuclideanSpace ℝ (Fin (1 + 2))) where
  generator x := lamPos • localGenerator 1 x
  nonzero x := smul_ne_zero lamPos_ne_zero (localGenerator_ne_zero 1 x)
  locallyRepresented x := by
    obtain ⟨U, K, hx, hUK, c, hc⟩ := localGenerator_locallyRepresented 1 x
    refine ⟨U, K, hx, hUK, lamPos • c, fun y hy hK => ?_⟩
    rw [map_smul, hc y hy hK]

theorem orientationScalar_pos : orientationScalar 1 posOrientation = lamPos := by
  unfold orientationScalar
  change (localTopAtIso 1 0).hom (lamPos • (localTopAtIso 1 0).inv (1 : ℚ)) = lamPos
  rw [map_smul]
  have := congrArg (fun f => f.hom (1 : ℚ)) (Iso.inv_hom_id (localTopAtIso 1 0))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at this
  rw [this, smul_eq_mul, mul_one]

/-- **The canonical ratio for the positive geometric orientation is `1`.** -/
theorem ratio_pos : lamPos / orientationScalar 1 posOrientation = 1 := by
  rw [orientationScalar_pos, div_self lamPos_ne_zero]

theorem euclidean_ratio_formula (c : AbF.obj ((chains E3).X 3)) (hc : RelCycle (Punctured 3) c) :
    (relCls (Punctured 3) c hc : (relativeChains (Punctured 3)).homology 3) =
      degRel c hc • (euclideanOrientation 1).generator 0 := by
  have h := relCls_eq_ratio_smul (euclideanOrientation 1) c hc
  rwa [orientationScalar_euclidean, div_one] at h


theorem simplex_relCycle_at (y : E3) (f : C(Dl, E3)) (hf : ∀ t ∈ bdry, f t ≠ y) :
    RelCycle ({y}ᶜ : Set E3) (sing (TopCat.of E3) (simpOf f)) := by
  rw [← chainMap_idSimplex]
  exact RelCycle.map f bdry ({y}ᶜ : Set E3) (fun t ht h0 => hf t ht h0) _ idSimplex_relCycle

theorem faces_avoid_at (y : E3) (w : Fin (3 + 1) → E3) (τ : Fin (3 + 1) → ℝ) (hτ : ∀ k, 0 < τ k)
    (hrel : ∑ k, τ k • (w k - y) = 0) (hdet : 0 < edgeDet w) :
    ∀ t ∈ bdry, affEMap w t ≠ y := by
  have hd : 0 < edgeDet (fun k => w k - y) := by rw [edgeDet_sub]; exact hdet
  have h := facesAvoid_of_rel (fun k => w k - y) τ hτ hrel hd
  intro t ht h0
  apply h t ht
  rw [affEMap_sub, h0, sub_self]

/-- The translation isomorphism of local homology at `y` is induced by the translation map. -/
theorem translate_hom_eq (y : E3) :
    (translateLocalHomologyIso 3 y 3).hom =
      homologyMap (relativeMap (Homeomorph.subRight y).toHomotopyEquiv.toFun
        ({y}ᶜ : Set E3) ({0}ᶜ : Set E3) (fun x hx => by
          simpa [Homeomorph.subRight_apply, sub_eq_zero] using hx)) 3 := by
  unfold translateLocalHomologyIso translateLocalIso
  rw [Functor.mapIso_hom, relativeHomeomorphIso_hom]
  rfl


/-- **Positive tetrahedra around any point represent the positive geometric generator.** -/
theorem tetra_generator_at (y : E3) (w : Fin (3 + 1) → E3) (τ : Fin (3 + 1) → ℝ)
    (hτ : ∀ k, 0 < τ k) (hrel : ∑ k, τ k • (w k - y) = 0) (hdet : 0 < edgeDet w) :
    (relCls ({y}ᶜ : Set E3) (sing (TopCat.of E3) (simpOf (affEMap w)))
        (simplex_relCycle_at y (affEMap w) (faces_avoid_at y w τ hτ hrel hdet)) :
        (relativeChains ({y}ᶜ : Set E3)).homology 3) = posOrientation.generator y := by
  set E := translateLocalHomologyIso 3 y 3 with hE
  have hinj : Function.Injective E.hom.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hinj
  have hd : 0 < edgeDet (fun k => w k - y) := by rw [edgeDet_sub]; exact hdet
  have hfa := facesAvoid_of_rel (fun k => w k - y) τ hτ hrel hd
  have hc0 : RelCycle ({0}ᶜ : Set E3) (sing (TopCat.of E3) (simpOf (affEMap (fun k => w k - y)))) :=
    simplex_relCycle _ hfa
  -- left side
  have hL : E.hom.hom (relCls ({y}ᶜ : Set E3) (sing (TopCat.of E3) (simpOf (affEMap w)))
      (simplex_relCycle_at y (affEMap w) (faces_avoid_at y w τ hτ hrel hdet))) =
      relCls ({0}ᶜ : Set E3) (sing (TopCat.of E3) (simpOf (affEMap (fun k => w k - y)))) hc0 := by
    rw [hE, translate_hom_eq]
    have hmaps : Set.MapsTo (Homeomorph.subRight y).toHomotopyEquiv.toFun ({y}ᶜ : Set E3) ({0}ᶜ : Set E3) :=
      fun x hx => by simpa [Homeomorph.subRight_apply, sub_eq_zero] using hx
    have hcy := simplex_relCycle_at y (affEMap w) (faces_avoid_at y w τ hτ hrel hdet)
    have h1 := relCls_map (Homeomorph.subRight y).toHomotopyEquiv.toFun ({y}ᶜ : Set E3) ({0}ᶜ : Set E3)
      hmaps _ hcy (RelCycle.map _ _ _ hmaps _ hcy)
    have hch : AbF.map ((chainMap (Homeomorph.subRight y).toHomotopyEquiv.toFun).f 3)
        (sing (TopCat.of E3) (simpOf (affEMap w))) =
        sing (TopCat.of E3) (simpOf (affEMap (fun k => w k - y))) := by
      change ((chainMap (Homeomorph.subRight y).toHomotopyEquiv.toFun).f 3).hom _ = _
      rw [chainMap_sing]
      congr 1
      apply ((TopCat.of E3).toSSetObjEquiv _).injective
      refine ContinuousMap.ext (fun t => ?_)
      change (Homeomorph.subRight y).toHomotopyEquiv.toFun (affEMap w t) = affEMap (fun k => w k - y) t
      rw [affEMap_sub]
      rfl
    exact h1.trans (relCls_congr _ _ _ _ _ hch)
  have hR : E.hom.hom (posOrientation.generator y) = lamPos • (localTopIso 1).inv.hom (1 : ℚ) := by
    change E.hom.hom (lamPos • (localTopAtIso 1 y).inv (1 : ℚ)) = _
    rw [map_smul]
    congr 1
    change E.hom.hom ((E ≪≫ localTopIso 1).inv.hom (1 : ℚ)) = _
    simp
  rw [hL, hR]
  have := relCls_eq_degRel_smul _ hc0
  rw [this]
  have hu : degRel (sing (TopCat.of E3) (simpOf (affEMap (fun k => w k - y)))) hc0 = lamPos :=
    degAff_universal _ hfa τ hτ hrel hd
  rw [hu]

end TernaryPeriodPolynomials.Argument.Lemma33.Orient
