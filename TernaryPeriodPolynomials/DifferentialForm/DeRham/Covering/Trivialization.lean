module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Extension

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter ContinuousAlternatingMap SmoothLocalDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (S : Space) {n : ℕ}

/-- Restrict an equivariant form to the distinguished actual lifting sheet. -/
def chartRestrict (n : ℕ) : EquivariantForm ρ (quotientChart S).source n →ₗ[ℝ]
    Form (F := F) (quotientChart S).target n :=
  (restrictTo (quotientChart_target_liftedDomain S) n).comp (equivariantSubmodule ρ _ n).subtype

@[simp] theorem chartRestrict_apply (w : EquivariantForm ρ (quotientChart S).source n)
    {x : Coordinates} (hx : x ∈ (quotientChart S).target) :
    (chartRestrict ρ S n w : RawForm Coordinates F n) x = (w.val : RawForm Coordinates F n) x :=
  restrictTo_apply (quotientChart_target_liftedDomain S) w.val hx

theorem chartRestrict_extend (w : Form (F := F) (quotientChart S).target n) :
    chartRestrict ρ S n (chartExtend ρ S n w) = w := by
  apply Form.ext
  intro x hx
  rw [chartRestrict_apply ρ S _ hx, chartExtend_apply ρ S _ (quotientChart_target_liftedDomain S hx)]
  have he : baseCoordinate S =ᶠ[𝓝 x] id := by
    filter_upwards [(quotientChart S).open_target.mem_nhds hx] with y hy
    exact baseCoordinate_chart S hy
  rw [extendRaw, sheetElement_chart S hx, coefficientFormMap_one,
    pullRaw_eventuallyEq _ he, pullRaw_id]

theorem chartExtend_restrict (w : EquivariantForm ρ (quotientChart S).source n) :
    chartExtend ρ S n (chartRestrict ρ S n w) = w := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  rw [chartExtend_apply ρ S _ hx]
  have hs := liftedDomain_isOpen (quotientChart S).open_source
  have hb := baseCoordinate_mem S hx
  have hbp := quotientChart_target_subset S hb
  have hbd := ((baseCoordinate_smooth S x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have hgd := ((deckMap_smooth (sheetElement S x) _ hbp).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hbp)).differentiableAt (by simp)
  have he := w.property (sheetElement S x) (baseCoordinate S x) (quotientChart_target_liftedDomain S hb)
  calc
    extendRaw ρ S (chartRestrict ρ S n w : RawForm Coordinates F n) x =
        coefficientFormMap (coefficientMap ρ (sheetElement S x)) n
          (pullRaw (baseCoordinate S) (w.val : RawForm Coordinates F n) x) := by
      unfold extendRaw pullRaw
      rw [chartRestrict_apply ρ S w hb]
    _ = pullRaw (baseCoordinate S) (pullRaw (deckMap (sheetElement S x))
          (w.val : RawForm Coordinates F n)) x := by
      change _ = (pullRaw (deckMap (sheetElement S x)) (w.val : RawForm Coordinates F n)
        (baseCoordinate S x)).compContinuousLinearMap _
      rw [he]
      ext v
      rfl
    _ = (w.val : RawForm Coordinates F n) x := by
      rw [pullRaw_comp _ hgd hbd,
        pullRaw_eventuallyEq _ (deckMap_baseCoordinate_eventually S hx), pullRaw_id]

/-- Genuine local trivialization: actual equivariant forms and ordinary smooth chart forms
are linearly equivalent, using the true deck sheets and their coefficient action. -/
def chartTrivialization (n : ℕ) : EquivariantForm ρ (quotientChart S).source n ≃ₗ[ℝ]
    Form (F := F) (quotientChart S).target n :=
  LinearEquiv.ofLinearMap (chartRestrict ρ S n) (chartExtend ρ S n)
    (LinearMap.ext (chartRestrict_extend ρ S)) (LinearMap.ext (chartExtend_restrict ρ S))

/-- The local trivialization intertwines the literal exterior differentials. -/
theorem chartRestrict_d (w : EquivariantForm ρ (quotientChart S).source n) :
    chartRestrict ρ S (n + 1) (differential ρ (quotientChart S).open_source n w) =
      d (quotientChart S).open_target n (chartRestrict ρ S n w) :=
  restrictTo_d (liftedDomain_isOpen (quotientChart S).open_source)
    (quotientChart S).open_target (quotientChart_target_liftedDomain S) w.val

theorem chartExtend_d (w : Form (F := F) (quotientChart S).target n) :
    chartExtend ρ S (n + 1) (d (quotientChart S).open_target n w) =
      differential ρ (quotientChart S).open_source n (chartExtend ρ S n w) := by
  apply (chartTrivialization ρ S (n + 1)).injective
  change chartRestrict ρ S (n + 1) _ = chartRestrict ρ S (n + 1) _
  rw [chartRestrict_extend, chartRestrict_d, chartRestrict_extend]

end TernaryPoly.SmoothCoveringDeRham
