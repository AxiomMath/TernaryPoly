module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FrameData

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory TopologicalSpace Set
open FreeActionLinearization CoveringSingularOrbits
open scoped Simplicial
variable {G : Type} [Group G] {X Y : TopCat.{0}}
  [MulAction G X] [ContinuousConstSMul G X] (T : SingularFrame G X Y)

/-- The actual constant sheet label of a connected singular simplex. -/
def simplexLabel (n : ℕ) (σ : SingularSimplex X n) : G :=
  T.label (TopCat.toSSetObjEquiv X (.op ⦋n⦌) σ (vertex n))

omit [ContinuousConstSMul G X] in
/-- The frame label is constant at all points of each actual singular simplex. -/
theorem simplexLabel_eq (n : ℕ) (σ : SingularSimplex X n) (a : Convexity.StdSimplex ℝ (Fin (n+1))) :
    T.label (TopCat.toSSetObjEquiv X (.op ⦋n⦌) σ a) = simplexLabel T n σ :=
  (T.label.isLocallyConstant.comp_continuous (TopCat.toSSetObjEquiv X (.op ⦋n⦌) σ).continuous).apply_eq_of_isPreconnected isPreconnected_univ (mem_univ a) (mem_univ (vertex n))

omit [ContinuousConstSMul G X] in
/-- Every face retains the true sheet label of the simplex. -/
theorem simplexLabel_face (n : ℕ) (σ : SingularSimplex X (n+1)) (i : Fin (n+2)) :
    simplexLabel T n ((TopCat.toSSet.obj X).δ i σ) = simplexLabel T (n+1) σ := by
  unfold simplexLabel
  rw [TopCat.toSSetObjEquiv_δ_apply]
  exact simplexLabel_eq T (n+1) σ _

/-- Actual deck translation multiplies the actual sheet label on the left. -/
theorem simplexLabel_smul (n : ℕ) (σ : SingularSimplex X n) (g : G) :
    simplexLabel T n (g • σ) = g * simplexLabel T n σ := by
  unfold simplexLabel
  rw [singularEquiv_smul]
  exact T.label_action g _

omit [ContinuousConstSMul G X] in
/-- The selected lift of a singular simplex has identity deck label. -/
theorem simplexLabel_lift (n : ℕ) (σ : SingularSimplex Y n) :
    simplexLabel T n (projection T.lift n σ) = 1 := T.label_lift _

/-- The actual projection from the covering frame forgets deck translation. -/
theorem frameProjection_smul (n : ℕ) (σ : SingularSimplex X n) (g : G) :
    projection T.base n (g • σ) = projection T.base n σ := by
  apply (TopCat.toSSetObjEquiv Y (.op ⦋n⦌)).injective
  rw [projection_equiv, projection_equiv, singularEquiv_smul]
  apply ContinuousMap.ext
  intro a
  exact T.base_action g _

omit [ContinuousConstSMul G X] in
/-- The actual chosen simplex lift is a section of frame projection. -/
theorem frameProjection_lift (n : ℕ) (σ : SingularSimplex Y n) :
    projection T.base n (projection T.lift n σ) = σ := by
  apply (TopCat.toSSetObjEquiv Y (.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro a
  exact T.base_lift _

/-- An actual singular simplex reconstructs from its selected lift and its constant true sheet label. -/
theorem simplex_frame_reconstruction (n : ℕ) (σ : SingularSimplex X n) :
    simplexLabel T n σ • projection T.lift n (projection T.base n σ) = σ := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).injective
  rw [singularEquiv_smul]
  apply ContinuousMap.ext
  intro a
  change simplexLabel T n σ • T.lift (T.base (TopCat.toSSetObjEquiv X (.op ⦋n⦌) σ a)) = _
  rw [← simplexLabel_eq T n σ a]
  exact T.reconstruction _

end TernaryPoly.SmoothSingularGlobal
