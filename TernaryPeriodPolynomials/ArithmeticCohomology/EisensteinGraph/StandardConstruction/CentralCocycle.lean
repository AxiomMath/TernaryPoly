module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-! Ported from the Sol reference implementation. -/

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CentralCocycle

/-- A central element with a nontrivial scalar action gives an explicit primitive. -/
theorem coboundary {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (action : G → V →ₗ[ℂ] V) (cocycle : G → V)
    (closed : ∀ g h, cocycle (g * h) = cocycle g + action g (cocycle h))
    (central : G) (commutes : ∀ g, central * g = g * central)
    (scalar : ℂ) (scalarAction : ∀ g, action central (cocycle g) = scalar • cocycle g)
    (nontrivial : scalar ≠ 1) (g : G) :
    cocycle g = action g ((scalar - 1)⁻¹ • cocycle central) -
      (scalar - 1)⁻¹ • cocycle central := by
  have equality : cocycle central + scalar • cocycle g =
      cocycle g + action g (cocycle central) := by
    rw [← scalarAction, ← closed, commutes, closed]
  have relation : (scalar - 1) • cocycle g = action g (cocycle central) - cocycle central := by
    calc
      _ = (cocycle central + scalar • cocycle g) - cocycle central - cocycle g := by
        rw [sub_smul, one_smul]
        abel
      _ = _ := by rw [equality]; abel
  calc
    cocycle g = (scalar - 1)⁻¹ • ((scalar - 1) • cocycle g) := by
      rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr nontrivial), one_smul]
    _ = _ := by rw [relation, smul_sub, map_smul]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CentralCocycle
