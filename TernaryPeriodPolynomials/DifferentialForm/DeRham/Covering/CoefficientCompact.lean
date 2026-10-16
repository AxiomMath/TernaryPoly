module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CoefficientMap

@[expose] public section


/-! Coefficient transport preserves genuine quotient compact support and its differential. -/
noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set SmoothLocalDeRham SymmetricSpaceCharts SymmetricSpaceCovering
variable {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

def coefficientCompactForm (ρ : Representation ℝ DeckGroup F) (σ : Representation ℝ DeckGroup G)
    (L : F →L[ℝ] G) (hL : ∀ g v, L (ρ g v) = σ g (L v)) (U : Set OrbitSpace) (k : ℕ) :
    CompactSupportForm ρ U k →ₗ[ℝ] CompactSupportForm σ U k where
  toFun w := ⟨coefficientEquivariantForm ρ σ L hL U k w.val,
    w.property.1.of_isClosed_subset isClosed_closure (quotientSupport_coefficientEquivariantForm ρ σ L hL U k w.val),
    (quotientSupport_coefficientEquivariantForm ρ σ L hL U k w.val).trans w.property.2⟩
  map_add' a b := Subtype.ext ((coefficientEquivariantForm ρ σ L hL U k).map_add a.val b.val)
  map_smul' c a := Subtype.ext ((coefficientEquivariantForm ρ σ L hL U k).map_smul c a.val)

theorem coefficientCompactForm_d (ρ : Representation ℝ DeckGroup F) (σ : Representation ℝ DeckGroup G)
    (L : F →L[ℝ] G) (hL : ∀ g v, L (ρ g v) = σ g (L v))
    {U : Set OrbitSpace} (hU : IsOpen U) (k : ℕ) (w : CompactSupportForm ρ U k) :
    coefficientCompactForm ρ σ L hL U (k+1) (compactDifferential ρ hU k w) =
      compactDifferential σ hU k (coefficientCompactForm ρ σ L hL U k w) :=
  Subtype.ext (coefficientEquivariantForm_d ρ σ L hL hU k w.val)

theorem coefficientEquivariantForm_inverse
    (ρ : Representation ℝ DeckGroup F) (σ : Representation ℝ DeckGroup G)
    (e : F ≃L[ℝ] G) (he : ∀ g v, e (ρ g v) = σ g (e v))
    (hi : ∀ g v, e.symm (σ g v) = ρ g (e.symm v))
    (U : Set OrbitSpace) (k : ℕ) (w : EquivariantForm ρ U k) :
    coefficientEquivariantForm σ ρ e.symm.toContinuousLinearMap hi U k
      (coefficientEquivariantForm ρ σ e.toContinuousLinearMap he U k w) = w := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  ext v
  exact e.symm_apply_apply (w.val.val x v)

end TernaryPoly.SmoothCoveringDeRham
