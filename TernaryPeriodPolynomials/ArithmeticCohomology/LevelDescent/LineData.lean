module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelDescent.RestrictCusp
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.FrameLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeUniq

@[expose] public section


/-!
# The concrete data of the restriction of a line face from level `N` to level `M`

Formalized by Claude Sonnet 5.5.

For `N ∣ M`, `M = N k`: the inclusion `Γ_{h⁻¹Qh}(M) ⊆ Γ_{h⁻¹Qh}(N)`, the scaling `r ↦ r^k` of the radical lattices,
and the compatibilities with the extension data of `lineFaceExt`.
-/

open scoped MatrixGroups
noncomputable section

namespace TernaryPeriodPolynomials.Argument.LevelDescent

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

/-- The scaling `r ↦ r^k` of the radical lattice. -/
def radScale (k : ℕ) : RadicalLattice →* RadicalLattice := powMonoidHom k

theorem radDet_radScale (k : ℕ) : radDet (radScale k) = (k : ℤ) * k := by
  simp [radDet, radScale, rl1, rl2, radicalLatticeFirst, radicalLatticeSecond]

theorem Gamma_le_of_dvd {N M : ℕ} (h : N ∣ M) : Gamma M ≤ Gamma N := by
  intro γ hγ
  rw [Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have key : ∀ x : ℤ, ((x : ZMod M)) = 0 → (x : ZMod N) = 0 := by
    intro x hx
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx ⊢
    exact (Int.natCast_dvd_natCast.mpr h).trans hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := h1; rw [← sub_eq_zero] at this ⊢
    have h' := key ((γ 0 0 : ℤ) - 1) (by push_cast; exact this)
    simpa using h'
  · exact key _ h2
  · exact key _ h3
  · have := h4; rw [← sub_eq_zero] at this ⊢
    have h' := key ((γ 1 1 : ℤ) - 1) (by push_cast; exact this)
    simpa using h'

end TernaryPeriodPolynomials.Argument.LevelDescent
