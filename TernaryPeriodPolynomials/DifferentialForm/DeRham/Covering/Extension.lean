module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.PullbackAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter ContinuousAlternatingMap SmoothLocalDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (S : Space) {n : ℕ}

@[simp] theorem coefficientFormMap_one (w : Coordinates [⋀^Fin n]→L[ℝ] F) :
    coefficientFormMap (coefficientMap ρ 1) n w = w := by
  ext v
  simp [coefficientFormMap, coefficientMap]

theorem coefficientFormMap_mul (g h : DeckGroup) (w : Coordinates [⋀^Fin n]→L[ℝ] F) :
    coefficientFormMap (coefficientMap ρ (g * h)) n w =
      coefficientFormMap (coefficientMap ρ g) n (coefficientFormMap (coefficientMap ρ h) n w) := by
  ext v
  simp [coefficientFormMap, coefficientMap, Module.End.mul_apply]

/-- Extend a chart form using its actual locally constant sheet coefficient and the derivative
of the actual local-lift coordinate. -/
def extendRaw (w : RawForm Coordinates F n) : RawForm Coordinates F n :=
  fun x => coefficientFormMap (coefficientMap ρ (sheetElement S x)) n
    (pullRaw (baseCoordinate S) w x)

theorem extendRaw_eventually (w : RawForm Coordinates F n) {x : Coordinates}
    (hx : x ∈ liftedDomain (quotientChart S).source) :
    extendRaw ρ S w =ᶠ[𝓝 x]
      coefficientRaw (coefficientMap ρ (sheetElement S x)) (pullRaw (baseCoordinate S) w) := by
  filter_upwards [sheetElement_eventually S hx] with y hy
  simp only [extendRaw, coefficientRaw, hy]

theorem extendRaw_smooth {w : RawForm Coordinates F n}
    (hw : ContDiffOn ℝ ∞ w (quotientChart S).target) :
    ContDiffOn ℝ ∞ (extendRaw ρ S w) (liftedDomain (quotientChart S).source) := by
  have hs := liftedDomain_isOpen (quotientChart S).open_source
  have hp := pullRaw_smooth hs (baseCoordinate_smooth S) hw (fun _ hx => baseCoordinate_mem S hx)
  intro x hx
  exact (((coefficientRaw_smooth (coefficientMap ρ (sheetElement S x)) hp x hx).contDiffAt
    (hs.mem_nhds hx)).congr_of_eventuallyEq (extendRaw_eventually ρ S w hx)).contDiffWithinAt

theorem extendRaw_equivariant (w : RawForm Coordinates F n) :
    IsEquivariant ρ (quotientChart S).source (extendRaw ρ S w) := by
  intro g x hx
  have hs := liftedDomain_isOpen (quotientChart S).open_source
  have hgx := deckMap_liftedDomain g (quotientChart S).source hx
  have hg := ((deckMap_smooth g x hx.1).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx.1)).differentiableAt (by simp)
  have hb := ((baseCoordinate_smooth S _ hgx).contDiffAt
    (hs.mem_nhds hgx)).differentiableAt (by simp)
  have he : (baseCoordinate S ∘ deckMap g) =ᶠ[𝓝 x] baseCoordinate S := by
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx.1] with y hy
    exact baseCoordinate_deck S g hy
  calc
    pullRaw (deckMap g) (extendRaw ρ S w) x =
        coefficientFormMap (coefficientMap ρ (sheetElement S (deckMap g x))) n
          (pullRaw (deckMap g) (pullRaw (baseCoordinate S) w) x) := by ext v; rfl
    _ = coefficientFormMap (coefficientMap ρ (g * sheetElement S x)) n
          (pullRaw (baseCoordinate S) w x) := by
      rw [sheetElement_deck S g hx, pullRaw_comp w hb hg, pullRaw_eventuallyEq w he]
    _ = coefficientFormMap (coefficientMap ρ g) n (extendRaw ρ S w x) :=
      coefficientFormMap_mul ρ _ _ _

/-- Genuine equivariant extension from a distinguished quotient lifting chart. -/
def chartExtend (n : ℕ) : Form (F := F) (quotientChart S).target n →ₗ[ℝ]
    EquivariantForm ρ (quotientChart S).source n where
  toFun w := ⟨restrictForm (liftedDomain (quotientChart S).source)
    (extendRaw ρ S (w : RawForm Coordinates F n)) (extendRaw_smooth ρ S (Form.smooth w)), by
      intro g x hx
      change ((_ : RawForm Coordinates F n) (deckMap g x)).compContinuousLinearMap _ = _
      rw [restrictForm_apply _ _ (deckMap_liftedDomain g _ hx), restrictForm_apply _ _ hx]
      exact extendRaw_equivariant ρ S (w : RawForm Coordinates F n) g x hx⟩
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

@[simp] theorem chartExtend_apply (w : Form (F := F) (quotientChart S).target n)
    {x : Coordinates} (hx : x ∈ liftedDomain (quotientChart S).source) :
    ((chartExtend ρ S n w).val : RawForm Coordinates F n) x =
      extendRaw ρ S (w : RawForm Coordinates F n) x :=
  restrictForm_apply _ (extendRaw_smooth ρ S (Form.smooth w)) hx

end TernaryPoly.SmoothCoveringDeRham
