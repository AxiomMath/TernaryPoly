module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# Finite spectral recovery when there are no paper data

If no `CohomologicalCuspData n` exists, the automorphic line span is zero and the finite recovery
statement holds with the empty family. This is the degenerate case of
`cuspidal_finite_spectral_recovery`; together with the eigen-separation reduction it shows that
only nonempty families of cuspidal data carry content.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein

namespace TernaryPeriodPolynomials.HeckeCommutativity

theorem automorphicLineSpan_eq_bot_of_isEmpty (n : ℕ) [IsEmpty (CohomologicalCuspData n)] :
    automorphicLineSpan n = ⊥ := by
  unfold automorphicLineSpan
  rw [Submodule.span_eq_bot]
  rintro a ⟨D, _⟩
  exact isEmptyElim D

theorem finite_recovery_of_isEmpty (n : ℕ) [IsEmpty (CohomologicalCuspData n)]
    (p : CohomologicalCuspData n → Module.End ℂ (BoundaryCoordinates n trivialCharacter))
    (b : BoundaryCoordinates n trivialCharacter) (hb : b.2 ∈ automorphicLineSpan n) :
    ∃ (m : ℕ) (D : Fin m → CohomologicalCuspData n), ∑ i, (p (D i) b).2 = b.2 := by
  rw [automorphicLineSpan_eq_bot_of_isEmpty, Submodule.mem_bot] at hb
  exact ⟨0, Fin.elim0, by simp [hb]⟩

end TernaryPeriodPolynomials.HeckeCommutativity
