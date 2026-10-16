module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CoefficientCompact

@[expose] public section

/-! Literal smooth primitive existence is invariant under an equivariant continuous coefficient equivalence. -/
noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set SymmetricSpaceCovering
variable {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

def CompactExactInDegree (ρ : Representation ℝ DeckGroup F) (k : ℕ) : Prop :=
  ∀ a : CompactSupportForm ρ univ (k+1), compactDifferential ρ isOpen_univ (k+1) a = 0 →
    ∃ v : EquivariantForm ρ univ k, differential ρ isOpen_univ k v = a.val

theorem compactExact_coefficient_transport
    (ρ : Representation ℝ DeckGroup F) (σ : Representation ℝ DeckGroup G)
    (e : F ≃L[ℝ] G) (he : ∀ g v, e (ρ g v) = σ g (e v)) (k : ℕ)
    (h : CompactExactInDegree σ k) : CompactExactInDegree ρ k := by
  have hi (g : DeckGroup) (v : G) : e.symm (σ g v) = ρ g (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  intro a ha
  let b := coefficientCompactForm ρ σ e.toContinuousLinearMap he univ (k+1) a
  have hb : compactDifferential σ isOpen_univ (k+1) b = 0 :=
    (coefficientCompactForm_d ρ σ e.toContinuousLinearMap he isOpen_univ (k+1) a).symm.trans
      ((congrArg (coefficientCompactForm ρ σ e.toContinuousLinearMap he univ ((k+1)+1)) ha).trans (map_zero _))
  obtain ⟨v,hv⟩ := h b hb
  refine ⟨coefficientEquivariantForm σ ρ e.symm.toContinuousLinearMap hi univ k v,?_⟩
  exact (coefficientEquivariantForm_d σ ρ e.symm.toContinuousLinearMap hi isOpen_univ k v).symm.trans
    ((congrArg (coefficientEquivariantForm σ ρ e.symm.toContinuousLinearMap hi univ (k+1)) hv).trans
      (coefficientEquivariantForm_inverse ρ σ e he hi univ (k+1) a.val))

end TernaryPoly.SmoothCoveringDeRham
