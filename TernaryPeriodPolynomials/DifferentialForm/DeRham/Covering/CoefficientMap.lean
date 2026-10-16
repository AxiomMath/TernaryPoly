module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CompactSupport

@[expose] public section


/-! Genuine continuous linear coefficient transport of smooth equivariant forms. -/
noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set SmoothLocalDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff
variable {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

def coefficientSmoothForm (L : F →L[ℝ] G) (s : Set Coordinates) (k : ℕ) :
    Form (F := F) s k →ₗ[ℝ] Form (F := G) s k where
  toFun w := ⟨coefficientRaw L w.val,coefficientRaw_smooth L (Form.smooth w),by
    intro x hx
    change coefficientFormMap L k (w.val x) = 0
    rw [Form.outside w hx, map_zero]⟩
  map_add' a b := by
    apply Subtype.ext
    funext x
    exact (coefficientFormMap L k).map_add (a.val x) (b.val x)
  map_smul' c a := by
    apply Subtype.ext
    funext x
    exact (coefficientFormMap L k).map_smul c (a.val x)

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
theorem coefficientSmoothForm_d (L : F →L[ℝ] G) {s : Set Coordinates} (hs : IsOpen s)
    (k : ℕ) (w : Form (F := F) s k) :
    coefficientSmoothForm L s (k+1) (d hs k w) = d hs k (coefficientSmoothForm L s k w) := by
  apply Form.ext
  intro x hx
  change coefficientFormMap L (k+1) ((d hs k w).val x) =
    (d hs k (coefficientSmoothForm L s k w)).val x
  rw [d_apply hs w hx, d_apply hs _ hx]
  exact (extDeriv_coefficientRaw L (((Form.smooth w x hx).contDiffAt
    (hs.mem_nhds hx)).differentiableAt (by simp))).symm

def coefficientEquivariantForm (ρ : Representation ℝ DeckGroup F) (σ : Representation ℝ DeckGroup G)
    (L : F →L[ℝ] G) (hL : ∀ g v, L (ρ g v) = σ g (L v)) (U : Set OrbitSpace) (k : ℕ) :
    EquivariantForm ρ U k →ₗ[ℝ] EquivariantForm σ U k where
  toFun w := ⟨coefficientSmoothForm L (liftedDomain U) k w.val,by
    intro g x hx
    ext v
    exact (congrArg (fun a : Coordinates [⋀^Fin k]→L[ℝ] F => L (a v)) (w.property g x hx)).trans
      (hL g (w.val.val x v))⟩
  map_add' a b := Subtype.ext ((coefficientSmoothForm L (liftedDomain U) k).map_add a.val b.val)
  map_smul' c a := Subtype.ext ((coefficientSmoothForm L (liftedDomain U) k).map_smul c a.val)

theorem coefficientEquivariantForm_d (ρ : Representation ℝ DeckGroup F) (σ : Representation ℝ DeckGroup G)
    (L : F →L[ℝ] G) (hL : ∀ g v, L (ρ g v) = σ g (L v))
    {U : Set OrbitSpace} (hU : IsOpen U) (k : ℕ) (w : EquivariantForm ρ U k) :
    coefficientEquivariantForm ρ σ L hL U (k+1) (differential ρ hU k w) =
      differential σ hU k (coefficientEquivariantForm ρ σ L hL U k w) :=
  Subtype.ext (coefficientSmoothForm_d L (liftedDomain_isOpen hU) k w.val)

theorem quotientSupport_coefficientEquivariantForm
    (ρ : Representation ℝ DeckGroup F) (σ : Representation ℝ DeckGroup G)
    (L : F →L[ℝ] G) (hL : ∀ g v, L (ρ g v) = σ g (L v))
    (U : Set OrbitSpace) (k : ℕ) (w : EquivariantForm ρ U k) :
    quotientSupport (coefficientEquivariantForm ρ σ L hL U k w) ⊆ quotientSupport w := by
  apply closure_mono
  apply image_mono
  intro x hx
  change coefficientFormMap L k (w.val.val x) ≠ 0 at hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx
  exact (congrArg (coefficientFormMap L k) hx).trans (map_zero _)

end TernaryPoly.SmoothCoveringDeRham
