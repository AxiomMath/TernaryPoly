module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Transitions
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CompactSupport
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingExtension

@[expose] public section


/-! Actual extension of compactly supported chart forms to global quotient forms. -/
noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter SmoothLocalDeRham SmoothDeRhamGluing
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped ContDiff Topology
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (S : Space) {n : ℕ}

theorem quotientSupport_chartExtend_subset (w : Form (F := F) (quotientChart S).target n)
    (hw : HasCompactSupport (w : RawForm Coordinates F n))
    (hs : tsupport (w : RawForm Coordinates F n) ⊆ (quotientChart S).target) :
    quotientSupport (chartExtend ρ S n w) ⊆
      (quotientChart S).symm '' tsupport (w : RawForm Coordinates F n) := by
  have hK := hw.image_of_continuousOn ((quotientChart S).symm.continuousOn.mono hs)
  apply closure_minimal _ hK.isClosed
  rintro q ⟨x, hx, rfl⟩
  have hxU : x ∈ liftedDomain (quotientChart S).source := by
    by_contra hn
    exact hx (Form.outside (chartExtend ρ S n w).val hn)
  have hb : baseCoordinate S x ∈ tsupport (w : RawForm Coordinates F n) := by
    apply subset_tsupport
    intro hz
    apply hx
    rw [chartExtend_apply ρ S w hxU]
    ext v
    simp [extendRaw, pullRaw, hz, coefficientFormMap]
  exact ⟨baseCoordinate S x, hb, (quotientChart S).left_inv hxU.2⟩

/-- Extend through actual deck sheets, then genuinely extend by zero to the global quotient. -/
def compactChartExtend (w : Form (F := F) (quotientChart S).target n)
    (hw : HasCompactSupport (w : RawForm Coordinates F n))
    (hs : tsupport (w : RawForm Coordinates F n) ⊆ (quotientChart S).target) :
    CompactSupportForm ρ univ n :=
  compactZeroExtend (quotientChart S).open_source (subset_univ _) n
    ⟨chartExtend ρ S n w,
      (hw.image_of_continuousOn ((quotientChart S).symm.continuousOn.mono hs)).of_isClosed_subset
        isClosed_closure (quotientSupport_chartExtend_subset ρ S w hw hs),
      (quotientSupport_chartExtend_subset ρ S w hw hs).trans (by
        rintro q ⟨x, hx, rfl⟩
        exact (quotientChart S).map_target (hs hx))⟩

theorem quotientSupport_compactChartExtend (w : Form (F := F) (quotientChart S).target n)
    (hw : HasCompactSupport (w : RawForm Coordinates F n))
    (hs : tsupport (w : RawForm Coordinates F n) ⊆ (quotientChart S).target) :
    quotientSupport (compactChartExtend ρ S w hw hs).val ⊆
      (quotientChart S).symm '' tsupport (w : RawForm Coordinates F n) :=
  quotientSupport_chartExtend_subset ρ S w hw hs

/-- Extension recovers the exact input, including its zero values outside the chart. -/
theorem globalChartRepresentative_compactChartExtend
    (w : Form (F := F) (quotientChart S).target n)
    (hw : HasCompactSupport (w : RawForm Coordinates F n))
    (hs : tsupport (w : RawForm Coordinates F n) ⊆ (quotientChart S).target) :
    globalChartRepresentative ρ S n (compactChartExtend ρ S w hw hs).val = w := by
  apply Form.ext
  intro x hx
  rw [globalChartRepresentative_apply ρ S _ hx]
  change ((chartExtend ρ S n w).val : RawForm Coordinates F n) x = _
  have he := congrArg (fun z : Form (F := F) (quotientChart S).target n =>
    (z : RawForm Coordinates F n) x) (chartRestrict_extend ρ S w)
  rwa [chartRestrict_apply ρ S _ hx] at he

end TernaryPoly.SmoothCoveringDeRham
