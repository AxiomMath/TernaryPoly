module

public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Link.Defs
public import TernaryPeriodPolynomials.Building.BadVertex.Fibers
public import TernaryPeriodPolynomials.Building.BadVertex.Projection
public import TernaryPeriodPolynomials.Building.BadVertex.PrismSupport
public import TernaryPeriodPolynomials.Building.BadVertex.MixedCharts
public import TernaryPeriodPolynomials.Building.RankTwo.GoodFilling
public import TernaryPeriodPolynomials.Building.BadVertex.CoherentCharts

@[expose] public section


/-!
# Lemma A.1: block charts, the residue functional of the quotient, and lifts from `Z`

Formalized by Claude Sonnet 5.5.
Paper: Appendix A.2.

For a bad line `b = augmentedLine g 0` the covector `ℓ` descends to the functional
`phi g (v₀,v₁) = r₁ v₀ + r₂ v₁` on `ℤ² ⊗ 𝔽₃` (`r_j = columnResidue g j`); the paper's `Z` is
the good rank-two complex `RankTwoGoodComplex.good (phi g)`, and the projection
`p : L_b → Z` is `BadVertexProjection.vertex g`.  `blockGL q` is the integral basis change which
is the identity on `b` and acts on the quotient by `q ∈ GL₂(ℤ)`; the chart `g * blockGL q` has
the standard fibres over the lines of the rank-two frame `q`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixALink

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.AugmentedFrameComplex
  TernaryPoly.OrientedListChains TernaryPoly.GoodLinkExtraction TernaryPoly.CoherentPrismReduction
  TernaryPoly.BadVertexProjection

local instance instDecRLC : DecidableEq RationalLine := Classical.decEq _
local instance instDecRLTwoC : DecidableEq RankTwoAugmentedFrames.RationalLine2 := Classical.decEq _
local notation "res" => AugmentedBadFaces.columnResidue

/-! ### Block charts -/

/-- The matrix `1 ⊕ q`. -/
def blockMatrix (q : RankTwoAugmentedFrames.IntegralGL) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1,0,0;0,q.val 0 0,q.val 0 1;0,q.val 1 0,q.val 1 1]

theorem blockMatrix_det (q : RankTwoAugmentedFrames.IntegralGL) :
    (blockMatrix q).det = q.val.det := by
  simp only [blockMatrix,Matrix.det_fin_three,Matrix.det_fin_two]
  simp

/-- The integral basis change `1 ⊕ q`. -/
def blockGL (q : RankTwoAugmentedFrames.IntegralGL) : IntegralGL :=
  Matrix.nonsingInvUnit (blockMatrix q) (by
    rw [blockMatrix_det]
    exact (Matrix.isUnit_iff_isUnit_det _).mp q.isUnit)

theorem blockGL_val (q : RankTwoAugmentedFrames.IntegralGL) : (blockGL q).val = blockMatrix q := rfl

theorem blockGL_line_zero (g : IntegralGL) (q : RankTwoAugmentedFrames.IntegralGL) :
    augmentedLine (g * blockGL q) 0 = augmentedLine g 0 := by
  have hv : (blockGL q).val.mulVec (Pi.single 0 1) = Pi.single 0 1 := by
    change (blockMatrix q).mulVec (Pi.single 0 1) = _
    rw [Matrix.mulVec_single_one]
    funext r
    fin_cases r <;> rfl
  have he : template 0 = rationalVector (Pi.single 0 1) := by
    funext r
    fin_cases r <;> rfl
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * blockGL q) (template 0)} = _
  rw [map_mul,LinearEquiv.mul_apply,he,← rationalVector_mulVec,hv]
  rfl

theorem lowerGL_block (q : RankTwoAugmentedFrames.IntegralGL) (M : IntegralGL)
    (hM : M = blockGL q) (hz : ∀ i : Fin 2, M.val i.succ 0 = 0) : lowerGL M hz = q := by
  subst hM
  apply Units.ext
  change lowerBlock (blockGL q) = q.val
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem vertex_block (g : IntegralGL) (q : RankTwoAugmentedFrames.IntegralGL) (i : Fin 3) (k : ℤ) :
    vertex g (fiberLine (g * blockGL q) i k) = RankTwoAugmentedFrames.augmentedLine q i := by
  have hh := blockGL_line_zero g q
  rw [BadVertexCoherentCharts.fiber_projection g (g * blockGL q) hh i k,
    lowerGL_block q _ (inv_mul_cancel_left g (blockGL q))]

/-! ### The residue functional of the quotient -/

/-- The descent of the covector `ℓ` to the quotient by `b = augmentedLine g 0`. -/
def phi (g : IntegralGL) : RankTwoGoodComplex.Functional where
  toFun v := res g 1 * v 0 + res g 2 * v 1
  map_add' v w := by simp only [Pi.add_apply]; ring
  map_smul' c v := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

theorem phi_ne_zero (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val) : phi g ≠ 0 := by
  have hb : res g 0 = 0 := AugmentedBadFaces.bad_augmentedLine_residue g 0 hbad
  obtain ⟨j,hj⟩ := AugmentedBadFaces.exists_columnResidue_ne_zero g
  intro h0
  fin_cases j
  · exact hj hb
  · apply hj
    have := LinearMap.congr_fun h0 (Pi.single 0 1)
    simpa [phi] using this
  · apply hj
    have := LinearMap.congr_fun h0 (Pi.single 1 1)
    simpa [phi] using this

/-- Over a bad line, an ambient neighbour is Good exactly when its quotient line is Good for the
descended functional. -/
theorem good_iff_image (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (F : RationalLine) (hne : F ≠ augmentedLine g 0) (he : {augmentedLine g 0,F} ∈ ambient) :
    Good F.val ↔ RankTwoGoodComplex.Good (phi g) (vertex g F) := by
  obtain ⟨p,hp,hpq⟩ := BadVertexFibers.quotientLine_exists_chart (vertex g F)
  obtain ⟨k,hk⟩ := BadVertexFibers.exists_chart g p hp F hne (by convert he) hpq.symm
  have hs : Submodule.span ℚ {RankTwoAugmentedFrames.rationalVector p} = (vertex g F).val :=
    congrArg Subtype.val hpq
  rw [RankTwoGoodComplex.good_iff_primitive (phi g) (vertex g F) hp hs,← hk,
    BadVertexFibers.chart_good_iff g hbad p hp k]
  simp only [phi,RankTwoGoodComplex.reduction,LinearMap.coe_mk,AddHom.coe_mk]
  rw [mul_comm (res g 1),mul_comm (res g 2)]

/-- A line `{b,F}`-adjacent to the fixed bad line projects to a Good line if it is Good. -/
theorem mapsFaces_phi (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val) :
    OrientedChainMap.MapsFaces (vertex g) (badLink (augmentedLine g 0))
      (RankTwoGoodComplex.good (phi g)) := by
  classical
  intro s hs
  refine ⟨BadVertexProjection.mapsFaces g hbad s hs,?_⟩
  intro Q hQ
  obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp hQ
  have hs' := (mem_goodLink ambient _ _ s).mp hs
  have hFgood : Good F.val := hs'.2.2 F hF
  have hne : F ≠ augmentedLine g 0 := BadVertexProjectionChange.good_ne_base g hbad F hFgood
  have hF1 : ({augmentedLine g 0,F} : Finset RationalLine) ∈ ambient := by
    have hsub : ({augmentedLine g 0,F} : Finset RationalLine) ⊆ {augmentedLine g 0} ∪ s := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
      · exact Finset.mem_union_right _ hF
    exact (ambient.isRelLowerSet_faces hs'.2.1).2 hsub (by simp)
  exact (good_iff_image g hbad F hne hF1).mp hFgood

theorem fiber_ne_base (h : IntegralGL) (i : Fin 3) (k : ℤ) :
    fiberLine h i k ≠ augmentedLine h 0 := by
  rw [BadVertexFibers.prism_fiber_eq_chart]
  exact BadVertexFibers.chart_ne_base _ _ _ _

theorem fiber_edge_ambient (h : IntegralGL) (i : Fin 3) (k : ℤ) :
    {augmentedLine h 0,fiberLine h i k} ∈ ambient := by
  rw [BadVertexFibers.prism_fiber_eq_chart]
  convert BadVertexFibers.chart_ambient_edge _ _ _ _

/-- Goodness of a block-chart fibre is Goodness of the corresponding quotient line. -/
theorem good_block_iff (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (q : RankTwoAugmentedFrames.IntegralGL) (i : Fin 3) (k : ℤ) :
    Good (fiberLine (g * blockGL q) i k).val ↔
      RankTwoGoodComplex.Good (phi g) (RankTwoAugmentedFrames.augmentedLine q i) := by
  have hh := blockGL_line_zero g q
  have hne : fiberLine (g * blockGL q) i k ≠ augmentedLine g 0 := by
    rw [← hh]; exact fiber_ne_base _ _ _
  have he : {augmentedLine g 0,fiberLine (g * blockGL q) i k} ∈ ambient := by
    rw [← hh]; exact fiber_edge_ambient _ _ _
  rw [good_iff_image g hbad _ hne he,vertex_block]

end TernaryPeriodPolynomials.Argument.AppendixALink
