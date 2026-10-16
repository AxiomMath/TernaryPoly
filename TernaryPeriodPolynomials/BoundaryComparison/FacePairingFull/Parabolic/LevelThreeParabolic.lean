module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Parabolic.LevelThreeCusps

@[expose] public section


/-!
# Parabolic at `T` and `L` implies parabolic at every cusp of `Γ₁'(3)`

`parabolicCrossedH1 ρ` (classes of `H¹(Γ₁'(3), ρ)` trivial at `T` and `L`, the notion in which the
library proves parabolic Poincaré duality and the exact dimension) is contained in the classes
restricting to zero on the stabilizer of every rational cusp. Together with the library's reverse
inclusion `binaryParabolicH1_le` they are equal (`binaryParabolicH1_eq_parabolicCrossedH1`), so the
cuspidal condition "at all rational cusps" of the paper is the library's two-generator one.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ binaryArithmeticLevel V)

/-- A crossed cocycle trivial at `T` and `L` is trivial on the stabilizer of every rational cusp. -/
theorem vanishes_every_cusp (x : crossedCocycles ρ)
    (hx : ∃ u, x.val (upper 1) = ρ (upper 1) u - u)
    (hy : ∃ u, x.val (lower 1) = ρ (lower 1) u - u)
    (frame : GeneralLinearGroup (Fin 2) ℚ) :
    ∃ w, ∀ γ ∈ binaryCuspLevel frame, x.val γ = ρ γ w - w := by
  rcases exists_cusp_conj frame with ⟨h, hh⟩ | ⟨h, hh⟩
  · obtain ⟨w₁, hw₁⟩ := vanishes_cusp_one ρ x hx
    exact trivialOn_conj ρ x h⁻¹ (binaryCuspLevel 1 : Set binaryArithmeticLevel)
      (binaryCuspLevel frame : Set binaryArithmeticLevel) ⟨w₁, hw₁⟩
      (fun t ht => by simpa using hh t ht)
  · obtain ⟨w₁, hw₁⟩ := vanishes_cusp_swap ρ x hy
    exact trivialOn_conj ρ x h⁻¹ (binaryCuspLevel swapQ : Set binaryArithmeticLevel)
      (binaryCuspLevel frame : Set binaryArithmeticLevel) ⟨w₁, hw₁⟩
      (fun t ht => by simpa using hh t ht)

/-- `parabolicCrossedH1 ρ ≤` classes vanishing at every cusp. -/
theorem parabolicCrossedH1_le_cusps :
    parabolicCrossedH1 ρ ≤ ⨅ frame : GeneralLinearGroup (Fin 2) ℚ,
      (crossedPullbackH1 (binaryCuspLevel frame).subtype ρ).ker := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hc
  rw [Submodule.mem_iInf]
  intro frame
  rw [LinearMap.mem_ker]
  have hxT := (mem_parabolicCrossed_iff ρ x).mp hx
  exact (vanishesOn_mk_iff ρ (binaryCuspLevel frame) x).mpr
    (vanishes_every_cusp ρ x hxT.1 hxT.2 frame)

/-- **The cusp condition at every rational cusp is the parabolic condition at `T`, `L`.** -/
theorem binaryParabolicH1_eq_parabolicCrossedH1 (degree : ℕ) :
    binaryParabolicH1 degree = parabolicCrossedH1 (binaryArithmeticRepresentation degree) :=
  le_antisymm (binaryParabolicH1_le degree) (parabolicCrossedH1_le_cusps _)

end TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic
