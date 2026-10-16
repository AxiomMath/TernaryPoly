module

public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.LineIdent
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.PlaneIdent

@[expose] public section


/-!
# The literal Stokes lemma at `Γ(N)`, unconditionally

Formalized by Claude Sonnet 5.5.

`step2_of_dvd`: Step 2 (`OrbitIdentLine` and `OrbitIdentPlane`) holds at every level `M` with `6 ∣ M`, `3 ≤ M`, by `orbitIdentLine` and `orbitIdentPlane`.
`stokes_gammaN_literal_uncond`: the literal Lemma `ar:lem:stokes` at `Γ(N)` for every `N ≥ 3`, with no hypotheses beyond `3 ≤ N` (the level `lcm(N, 6)` is used internally).
-/

open scoped MatrixGroups
noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.RadicalInduction

variable {N M n : ℕ} [NeZero N] [NeZero M]

/-- **Step 2 at every level divisible by six.** -/
theorem step2_of_dvd (hM : 3 ≤ M) (h6 : 6 ∣ M) : Step2 M n hM :=
  ⟨orbitIdentLine M n hM h6, orbitIdentPlane M n hM h6⟩

/-- **The literal Lemma `ar:lem:stokes` at `Γ(N)`, every `N ≥ 3`, unconditionally.** -/
theorem stokes_gammaN_literal_uncond (hN : 3 ≤ N) (_hn : 4 ≤ n) : StokesGammaNLiteral N n hN := by
  have : NeZero (Nat.lcm N 6) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by norm_num)⟩
  have hM : 3 ≤ Nat.lcm N 6 :=
    le_trans hN (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (NeZero.ne N) (by norm_num))) (Nat.dvd_lcm_left N 6))
  exact stokes_gammaN_literal hN (step2_of_dvd hM (Nat.dvd_lcm_right N 6))

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
