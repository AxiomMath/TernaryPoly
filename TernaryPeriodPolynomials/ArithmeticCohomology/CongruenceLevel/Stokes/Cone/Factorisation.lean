module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeInst
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.QDiAlignInst
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LiteralGlobal

@[expose] public section


/-!
# Proposition C.5 at `Γ(N)` from one cone-level factorisation

Formalized by Claude Sonnet 5.5.

`ConeFactorisation M n hM hn A` is the single named input.  It says: for a class `c₀ ∈ H²(Γ(M), E_n)` with zero flag restrictions and boundary data `(ξ_P, ξ_Q)`, a dual Eisenstein class
`c' ∈ Hd`, and induced classes `c_V ∈ H²(Γ(6), Fun(Γ(6)/Γ(M), E_n))`, `c'_V` (Shapiro coordinates the transports of `c₀`, of the literal dual class `toLiteralG c'`), the Stokes sum of the
`Γ(6)` cone pairings over the faces `i` of `Γ(6)` and the `S_i`-orbits `O` of `Γ(6)/Γ(M)` (the `lineFacePairM`, `planeFacePairM` of the diagonal terms
`B_i(h2E e_O (res_i c_V), h2E e_Oᵀ (res_i c'_V))`, `LevelChangeInst.stokesSum`) equals the level-`M` expression
`pairP ξ_P (r_P c') + ∑_{i'} pairQfaceCan(ξ_{Q,i'}, eQ_{i'} (r_Q c')_{i'})` for some plane pairing `pairP`.
Given it, `stokesAtLevel_of_coneFactorisation` derives `StokesAtLevel` from `gamma6_stokes_ind_M` (Stokes at `Γ(6)` for the induced modules, zero flags of the induced classes by
`res_flag_ind_zero`, admissibility of the dual series by the `HdLit_zeroFlags`), and `propC5_gammaN_of_coneFactorisation` closes Proposition C.5 for every `Γ(N)`, `N ≥ 3`, `n ≥ 4`.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4

section CF

variable {M n : ℕ} [NeZero M]

/-- The finiteness of `Γ(6)/Γ(M)` as a `Fintype`. -/
instance Δ6_fintype : Fintype (↥(gammaN 6) ⧸ Δ6 M) := Fintype.ofFinite _

/-- The alignment `A` with the isomorphism at the line face `i` rescaled by the nonzero constant `κ i` (the per-face constants of the factorisation (a′) of the cone pairing). -/
def QDiAlignment.scale (A : QDiAlignment M n) (κ : LineFaces M → ℂ) (hκ : ∀ i, κ i ≠ 0) : QDiAlignment M n where
  eQ i := (A.eQ i).trans (LinearEquiv.smulOfNeZero ℂ (QDiLit M n i) (κ i) (hκ i))

theorem QDiAlignment.pairQ_scale (A : QDiAlignment M n) (κ : LineFaces M → ℂ) (hκ : ∀ i, κ i ≠ 0) (hM : 3 ≤ M)
    (i : LineFaces M) (a : lineFaceCuspidal M i.rep n) (b : QDi M n i) :
    (A.scale κ hκ).pairQ hM i a b = κ i * A.pairQ hM i a b := by
  change pairQfaceCan n hM i a (κ i • A.eQ i b) = κ i * pairQfaceCan n hM i a (A.eQ i b)
  rw [map_smul, smul_eq_mul]

/-- **Canonical-pairing form of the cone-level factorisation.**  The cone-level factorisation at level `M` (`6 ∣ M`): the Stokes sum of the
`Γ(6)` cone pairings of the induced classes equals the level-`M` canonical Stokes expression, for the canonical line pairings `pairQfaceCan` transported along the canonical alignment `qdiAlignmentInst`
and rescaled by nonzero per-face constants `κ` (the constants `c i` of (a′), transported to the faces of `Γ(M)` over the face `i` of `Γ(6)`), and some plane pairing.
It is the conjunction of (a′) `lineFacePairM = c · (S2's canonical pairing)` for the coefficient modules `Fun(Γ(6)/Γ(M), E)`, of the Mackey identification of the diagonal terms with the
`Γ(M)`-face pairings (the bijection between pairs `(i, O)` and the faces of `Γ(M)`, frame changes and the compatibility of the canonical pairing with finite-index induction), and the same for planes. -/
def ConeFactorisation (hM : 3 ≤ M) (hn : 4 ≤ n) : Prop :=
  ∃ (κ : LineFaces M → ℂ) (hκ : ∀ i, κ i ≠ 0), ∃ pairP : PlaneCuspSum M n →ₗ[ℂ] PDmod M n →ₗ[ℂ] ℂ,
    ∀ c₀ : groupCohomology.H2 (gammaNRepAll M n), ZeroFlags M n c₀ →
      ∀ (ξP : PlaneCuspSum M n) (ξQ : LineCuspSum M n),
        planeCuspSumEmbedding M n ξP = planeBoundary M n c₀ →
        lineCuspSumEmbedding M n ξQ = lineBoundary M n c₀ →
        ∀ c' : Hd (N := M) (n := n) hn,
          ∀ (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
            (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M)))),
            PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀ →
            PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
              (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
              (toLiteralG M n c'.1 : groupCohomology.H2 (Rep.of (gammaNRepAll M n).ρ.dual)) →
            stokesSum (rhoEn n) (Δ6 M) cV (h2Hom (dualRepHom (rhoEn n) (Δ6 M)) cVd) =
              pairP ξP (dualRP hn c') +
                sumPairing _ _ ((qdiAlignmentInst (M := M) (n := n)).scale κ hκ |>.pairQ hM) ξQ (dualRQ hM hn c')

/-- **Stokes at level `Γ(M)` from the cone-level factorisation.**  The alignment is the canonical one rescaled by the constants `κ`. -/
theorem stokesAtLevel_of_coneFactorisation (hM : 3 ≤ M) (hn : 4 ≤ n)
    (F : ConeFactorisation hM hn) :
    ∃ (κ : LineFaces M → ℂ) (hκ : ∀ i, κ i ≠ 0), StokesAtLevel hM hn ((qdiAlignmentInst (M := M) (n := n)).scale κ hκ) := by
  obtain ⟨κ, hκ, pairP, hP⟩ := F
  refine ⟨κ, hκ, pairP, fun c₀ hz ξP ξQ hξP hξQ c' => ?_⟩
  obtain ⟨cV, hcV⟩ := (PhiH_bijective (rhoEn n) (Δ6 M)).2
    (transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀)
  obtain ⟨cVd, hcVd⟩ := (PhiH_bijective (rhoEn n).dual (Δ6 M)).2
    (transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
      (toLiteralG M n c'.1 : groupCohomology.H2 (Rep.of (gammaNRepAll M n).ρ.dual)))
  have hd : toLiteralG M n c'.1 ∈ HdLit hn := by
    obtain ⟨u, hu⟩ := c'.2
    exact ⟨u, congrArg (toLiteralG M n) hu⟩
  have h0 := gamma6_stokes_ind_M M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀
    (toLiteralG M n c'.1 : groupCohomology.H2 (Rep.of (gammaNRepAll M n).ρ.dual))
    (fun g => hz g) (fun g => HdLit_zeroFlags hM hn _ hd g) cV hcV cVd hcVd
  rw [hP c₀ hz ξP ξQ hξP hξQ c' cV cVd hcV hcVd] at h0
  exact h0

end CF

/-- **Proposition C.5 for every `Γ(N)`, `N ≥ 3`, `n ≥ 4`, from the cone-level factorisation at the level `lcm(N, 6)`.** -/
theorem propC5_gammaN_of_coneFactorisation {N n : ℕ} [NeZero N] (hN : 3 ≤ N) (hn : 4 ≤ n)
    (F : ConeFactorisation (M := Nat.lcm N 6) (three_le_lcm hN) hn) :
    PropC5GammaN N n := by
  obtain ⟨κ, hκ, hS⟩ := stokesAtLevel_of_coneFactorisation (three_le_lcm hN) hn F
  exact propC5_gammaN_assembled hN hn (Nat.dvd_lcm_left N 6) (three_le_lcm hN)
    ⟨(qdiAlignmentInst (M := Nat.lcm N 6) (n := n)).scale κ hκ, hS⟩

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
