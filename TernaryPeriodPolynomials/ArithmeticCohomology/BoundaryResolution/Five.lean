module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Cone
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

@[expose] public section


noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison
open CategoryTheory Category Limits Abelian ComposableArrows HomologicalComplex HomologySequence

variable {C : Type*} [Category* C] [Abelian C]
  {S T : ShortComplex (ChainComplex C ℕ)} (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)
  [QuasiIso φ.τ₁] [QuasiIso φ.τ₃]

include hS hT in
/-- The missing middle form of the homology-sequence five lemma for nonnegative complexes. -/
theorem middle_quasiIso : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hm : Mono (homologyMap φ.τ₂ n) := by
    apply mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS hT (n+1) n (Cone.downRel n)))
    · exact (composableArrows₅_exact hS (n+1) n (Cone.downRel n)).δ₀.δ₀
    · exact (composableArrows₅_exact hT (n+1) n (Cone.downRel n)).δ₀.δ₀
    · exact inferInstanceAs (Epi (homologyMap φ.τ₃ (n+1)))
    · exact inferInstanceAs (Mono (homologyMap φ.τ₁ n))
    · exact inferInstanceAs (Mono (homologyMap φ.τ₃ n))
  have he : Epi (homologyMap φ.τ₂ n) := by
    cases n with
    | zero =>
      apply epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ 0)
      · exact composableArrows₂_exact hT 0
      · have : Epi S.g := hS.epi_g
        exact epi_homologyMap_of_epi_of_not_rel S.g 0 (by simp [ComplexShape.down_Rel])
      · exact inferInstanceAs (Epi (homologyMap φ.τ₁ 0))
      · exact inferInstanceAs (Epi (homologyMap φ.τ₃ 0))
    | succ n =>
      apply epi_of_epi_of_epi_of_mono
        ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS hT (n+1) n (Cone.downRel n)))
      · exact (composableArrows₅_exact hS (n+1) n (Cone.downRel n)).δlast.δlast
      · exact (composableArrows₅_exact hT (n+1) n (Cone.downRel n)).δlast.δlast
      · exact inferInstanceAs (Epi (homologyMap φ.τ₁ (n+1)))
      · exact inferInstanceAs (Epi (homologyMap φ.τ₃ (n+1)))
      · exact inferInstanceAs (Mono (homologyMap φ.τ₁ n))
  exact isIso_of_mono_of_epi _

end TernaryPoly.BoundaryFaceResolutionComparison
