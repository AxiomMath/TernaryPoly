module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Restriction

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter ContinuousAlternatingMap SmoothLocalDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (S : Space) {V : Set Coordinates} {n : ℕ}

theorem extendRaw_smoothOn (hV : IsOpen V) {w : RawForm Coordinates F n}
    (hw : ContDiffOn ℝ ∞ w V) : ContDiffOn ℝ ∞ (extendRaw ρ S w) (liftedDomain (chartOpen S V)) := by
  have hs := liftedDomain_isOpen (chartOpen_isOpen S hV)
  have hsub := liftedDomain_mono (chartOpen_subset S V)
  have hb := (baseCoordinate_smooth S).mono hsub
  have hp := pullRaw_smooth hs hb hw (fun _ hx => baseCoordinate_mem_chartOpen S hx)
  intro x hx
  exact (((coefficientRaw_smooth (coefficientMap ρ (sheetElement S x)) hp x hx).contDiffAt
    (hs.mem_nhds hx)).congr_of_eventuallyEq
      (extendRaw_eventually ρ S w (hsub hx))).contDiffWithinAt

/-- Extension over the genuine smaller quotient neighborhood cut out by V. -/
def chartExtendOn (hV : IsOpen V) (n : ℕ) : Form (F := F) V n →ₗ[ℝ]
    EquivariantForm ρ (chartOpen S V) n where
  toFun w := ⟨restrictForm (liftedDomain (chartOpen S V))
    (extendRaw ρ S (w : RawForm Coordinates F n)) (extendRaw_smoothOn ρ S hV (Form.smooth w)), by
      intro g x hx
      change ((_ : RawForm Coordinates F n) (deckMap g x)).compContinuousLinearMap _ = _
      rw [restrictForm_apply _ _ (deckMap_liftedDomain g _ hx), restrictForm_apply _ _ hx]
      exact extendRaw_equivariant ρ S (w : RawForm Coordinates F n) g x
        (liftedDomain_mono (chartOpen_subset S V) hx)⟩
  map_add' w z := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, AddMemClass.coe_add, Pi.add_apply]
    ext v
    simp [extendRaw, pullRaw, coefficientFormMap]
  map_smul' c w := by
    apply Subtype.ext
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
    ext v
    simp [extendRaw, pullRaw, coefficientFormMap]

@[simp] theorem chartExtendOn_apply (hV : IsOpen V) (w : Form (F := F) V n)
    {x : Coordinates} (hx : x ∈ liftedDomain (chartOpen S V)) :
    ((chartExtendOn ρ S hV n w).val : RawForm Coordinates F n) x =
      extendRaw ρ S (w : RawForm Coordinates F n) x :=
  restrictForm_apply _ (extendRaw_smoothOn ρ S hV (Form.smooth w)) hx

theorem chartExtendOn_d (hV : IsOpen V) (w : Form (F := F) V n) :
    differential ρ (chartOpen_isOpen S hV) n (chartExtendOn ρ S hV n w) =
      chartExtendOn ρ S hV (n + 1) (d hV n w) := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  have hs := liftedDomain_isOpen (chartOpen_isOpen S hV)
  have hsub := liftedDomain_mono (chartOpen_subset S V)
  have hb := baseCoordinate_mem_chartOpen S hx
  have hbc := (baseCoordinate_smooth S x (hsub hx)).contDiffAt
    ((liftedDomain_isOpen (quotientChart S).open_source).mem_nhds (hsub hx))
  have hw := ((Form.smooth w _ hb).contDiffAt (hV.mem_nhds hb)).differentiableAt (by simp)
  have hp := ((pullRaw_smooth hs ((baseCoordinate_smooth S).mono hsub) (Form.smooth w)
    (fun _ hy => baseCoordinate_mem_chartOpen S hy) x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have he : ((chartExtendOn ρ S hV n w).val : RawForm Coordinates F n) =ᶠ[𝓝 x]
      coefficientRaw (coefficientMap ρ (sheetElement S x))
        (pullRaw (baseCoordinate S) (w : RawForm Coordinates F n)) := by
    filter_upwards [hs.mem_nhds hx, extendRaw_eventually ρ S (w : RawForm Coordinates F n) (hsub hx)] with y hy hey
    rw [chartExtendOn_apply ρ S hV w hy, hey]
  change (d hs n (chartExtendOn ρ S hV n w).val : RawForm Coordinates F (n + 1)) x = _
  rw [d_apply hs _ hx, he.extDeriv_eq, extDeriv_coefficientRaw _ hp, extDeriv_pullRaw hbc hw,
    chartExtendOn_apply ρ S hV _ hx]
  unfold extendRaw pullRaw
  rw [d_apply hV w hb]

theorem chartExtendOn_restrict (hV : IsOpen V) (hVt : V ⊆ (quotientChart S).target)
    (w : EquivariantForm ρ (quotientChart S).source n) :
    chartExtendOn ρ S hV n (restrictTo hVt n (chartRestrict ρ S n w)) =
      restrictEquivariant ρ (chartOpen_subset S V) n w := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  have hb := baseCoordinate_mem_chartOpen S hx
  have hsub := liftedDomain_mono (chartOpen_subset S V) hx
  rw [chartExtendOn_apply ρ S hV _ hx, restrictEquivariant_apply ρ _ w hx]
  have he := congrArg (fun z : EquivariantForm ρ (quotientChart S).source n =>
    (z.val : RawForm Coordinates F n) x) (chartExtend_restrict ρ S w)
  rw [chartExtend_apply ρ S _ hsub] at he
  rw [← he]
  unfold extendRaw pullRaw
  rw [restrictTo_apply hVt _ hb]

end TernaryPoly.SmoothCoveringDeRham
