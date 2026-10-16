module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceTopologyComplete
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionGeometry
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.ChartsQuadrant

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels
  SymmetricSpaceBoundaryFaceTopology SingularBoundaryRestriction Topology

abbrev SignedModel := Vec3 × ℝ

def boundaryAxes : Set Corner := {p | p.2.1.val = 0 ∨ p.2.2.val = 0}

/-- Signed normal coordinate: positive is the line side, negative the plane side. -/
def signedAxesHomeomorph : SignedModel ≃ₜ boundaryAxes where
  toFun p := ⟨(p.1, ⟨max (-p.2) 0, show (0 : ℝ) ≤ max (-p.2) 0 from le_max_right _ _⟩, ⟨max p.2 0, show (0 : ℝ) ≤ max p.2 0 from le_max_right _ _⟩), by
    rcases le_total 0 p.2 with h | h
    · exact Or.inl (max_eq_right (neg_nonpos.mpr h))
    · exact Or.inr (max_eq_right h)⟩
  invFun p := (p.val.1, p.val.2.2.val - p.val.2.1.val)
  left_inv p := by
    refine Prod.ext rfl ?_
    exact SymmetricSpaceBoundaryCharts.max_sub_max_neg p.2
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    apply Prod.ext <;> apply Subtype.ext
    · change max (-(p.val.2.2.val - p.val.2.1.val)) 0 = p.val.2.1.val
      rcases p.property with h | h
      · simp only [h, sub_zero, max_eq_right (neg_nonpos.mpr (show (0 : ℝ) ≤ p.val.2.2.val from p.val.2.2.property))]
      · simp only [h, zero_sub, neg_neg, max_eq_left (show (0 : ℝ) ≤ p.val.2.1.val from p.val.2.1.property)]
    · change max (p.val.2.2.val - p.val.2.1.val) 0 = p.val.2.2.val
      rcases p.property with h | h
      · simp only [h, sub_zero, max_eq_left (show (0 : ℝ) ≤ p.val.2.2.val from p.val.2.2.property)]
      · simp only [h, zero_sub, max_eq_right (neg_nonpos.mpr (show (0 : ℝ) ≤ p.val.2.1.val from p.val.2.1.property))]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Actual rational boundary chart in signed-normal coordinates. -/
def signedParam (g : RationalGL) : SignedModel → BoundaryCover := fun p =>
  ⟨chart g (signedAxesHomeomorph p).val,
    (chart_boundary_iff g _).mpr (signedAxesHomeomorph p).property⟩

theorem signedParam_isEmbedding (g : RationalGL) : IsEmbedding (signedParam g) :=
  ((chart_isOpenEmbedding g).isEmbedding.comp
    (IsEmbedding.subtypeVal.comp signedAxesHomeomorph.isEmbedding)).codRestrict upstairsBoundary
      (fun p => (chart_boundary_iff g _).mpr (signedAxesHomeomorph p).property)

theorem signedParam_range (g : RationalGL) :
    Set.range (signedParam g) = Subtype.val ⁻¹' Set.range (chart g) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(signedAxesHomeomorph p).val, rfl⟩
  · rintro ⟨p, hp⟩
    have hb : p ∈ boundaryAxes := (chart_boundary_iff g p).mp (hp ▸ x.property)
    refine ⟨signedAxesHomeomorph.symm ⟨p, hb⟩, Subtype.ext ?_⟩
    change chart g (signedAxesHomeomorph (signedAxesHomeomorph.symm ⟨p, hb⟩)).val = x.val
    simpa only [Homeomorph.apply_symm_apply] using hp

theorem signedParam_isOpenEmbedding (g : RationalGL) : IsOpenEmbedding (signedParam g) := by
  refine ⟨signedParam_isEmbedding g, ?_⟩
  rw [signedParam_range]
  exact (chart_range_open g).preimage continuous_subtype_val

def signedChart (g : RationalGL) : OpenPartialHomeomorph BoundaryCover SignedModel :=
  ((signedParam_isOpenEmbedding g).toOpenPartialHomeomorph (signedParam g)).symm

@[simp] theorem signedChart_source (g : RationalGL) :
    (signedChart g).source = Subtype.val ⁻¹' Set.range (chart g) := by simp [signedChart, signedParam_range]

@[simp] theorem signedChart_target (g : RationalGL) : (signedChart g).target = Set.univ := by
  simp [signedChart]

@[simp] theorem signedChart_apply_param (g : RationalGL) (p : SignedModel) :
    signedChart g (signedParam g p) = p :=
  (signedParam_isOpenEmbedding g).toOpenPartialHomeomorph_left_inv _

/-- The positive closed side is exactly the actual chart line face. -/
theorem signedParam_line_iff (g : RationalGL) (p : SignedModel) (L : Line) :
    (signedParam g p).val ∈ lineFace L ↔ 0 ≤ p.2 ∧ lineLabel g = L := by
  rw [signedParam, lineFace_chart_iff]
  change (max (-p.2) 0 = 0 ∧ lineLabel g = L) ↔ _
  rw [max_eq_right_iff, neg_nonpos]

theorem signedParam_plane_iff (g : RationalGL) (p : SignedModel) (P : Plane) :
    (signedParam g p).val ∈ planeFace P ↔ p.2 ≤ 0 ∧ planeLabel g = P := by
  rw [signedParam, planeFace_chart_iff]
  change (max p.2 0 = 0 ∧ planeLabel g = P) ↔ _
  rw [max_eq_right_iff]

theorem signedParam_openLine_iff (g : RationalGL) (p : SignedModel) (L : Line) :
    (signedParam g p).val ∈ openLineFace L ↔ 0 < p.2 ∧ lineLabel g = L := by
  rw [signedParam, openLineFace_chart_iff]
  change ((max (-p.2) 0 = 0 ∧ 0 < max p.2 0) ∧ lineLabel g = L) ↔ _
  rw [max_eq_right_iff, neg_nonpos, lt_max_iff]
  simp only [lt_self_iff_false, or_false]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · exact fun h => ⟨⟨h.1.le, h.1⟩, h.2⟩

theorem signedParam_openPlane_iff (g : RationalGL) (p : SignedModel) (P : Plane) :
    (signedParam g p).val ∈ openPlaneFace P ↔ p.2 < 0 ∧ planeLabel g = P := by
  rw [signedParam, openPlaneFace_chart_iff]
  change ((0 < max (-p.2) 0 ∧ max p.2 0 = 0) ∧ planeLabel g = P) ↔ _
  rw [max_eq_right_iff, lt_max_iff]
  simp only [lt_self_iff_false, or_false, neg_pos]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, h.1.le⟩, h.2⟩

/-- At zero normal parameter the chart is exactly the proved whole flag model. -/
@[simp] theorem signedParam_zero (g : RationalGL) (u : Vec3) :
    (signedParam g (u, 0)).val = chart g (u, zeroRoot, zeroRoot) := by
  simp [signedParam, signedAxesHomeomorph, zeroRoot]

end TernaryPoly.SymmetricSpaceBoundaryMV
