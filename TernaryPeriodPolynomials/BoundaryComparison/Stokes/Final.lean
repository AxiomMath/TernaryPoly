module

public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.Descent
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelDescent.LineCan
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelDescent.PlaneCan

@[expose] public section


/-!
# The literal Stokes lemma at `Γ(N)`, all `N ≥ 3`

Formalized by Claude Sonnet 5.5.  Paper: Lemma `ar:lem:stokes`.

`restrictionIdent`: the restriction identities (`LevelDescent.canAtClass_restrict`, line faces) and their plane twin (`canAtClassP_restrict`) give `RestrictionIdent N M n` for `N ∣ M`, with `R = resLevel`, `R' = resLevelDual`.
`stokes_gammaN_literal`: for every `N ≥ 3`, `StokesGammaNLiteral N n`, from Step 2 (`OrbitIdentLine/Plane`) at the level `lcm(N, 6)` (the only input).
-/

open scoped MatrixGroups
noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.LevelDescent

variable {N M n : ℕ} [NeZero N] [NeZero M]

theorem restrictionIdent (hN : 3 ≤ N) (hM : 3 ≤ M) (hNM : N ∣ M) : RestrictionIdent N M n hN hM :=
  ⟨resLevel N M n hNM, resLevelDual n hNM, fun a ha => zeroFlags_resLevel N M n hNM a ha,
    fun b hb => zeroFlags_resLevelDual n hNM b hb,
    fun a ha b hb h => canAtClass_restrict hNM h n hN hM a ha b hb,
    fun a ha b hb h => canAtClassP_restrict hNM h n hN hM a ha b hb⟩

/-- **The literal Lemma `ar:lem:stokes` at `Γ(N)`, every `N ≥ 3`**: `ε_P ∑_P ⟨r_P a, r_P b⟩_P + ε_Q ∑_Q ⟨r_Q a, r_Q b⟩_Q = 0` with the canonical face pairings.
Its only input is Step 2 (`OrbitIdentLine/Plane`) at the level `lcm(N, 6)`. -/
theorem stokes_gammaN_literal (hN : 3 ≤ N)
    (S2 : @Step2 (Nat.lcm N 6) n ⟨Nat.lcm_ne_zero (NeZero.ne N) (by norm_num)⟩
      (le_trans hN (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (NeZero.ne N) (by norm_num))) (Nat.dvd_lcm_left N 6)))) :
    StokesGammaNLiteral N n hN := by
  have : NeZero (Nat.lcm N 6) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by norm_num)⟩
  have hM : 3 ≤ Nat.lcm N 6 :=
    le_trans hN (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (NeZero.ne N) (by norm_num))) (Nat.dvd_lcm_left N 6))
  exact stokesGammaNLiteral_of_restriction hN hM (Nat.dvd_lcm_left N 6) (Nat.dvd_lcm_right N 6) S2
    (restrictionIdent hN hM (Nat.dvd_lcm_left N 6))

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
