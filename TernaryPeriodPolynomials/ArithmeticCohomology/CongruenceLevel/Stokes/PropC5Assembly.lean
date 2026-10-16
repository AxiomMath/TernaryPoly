module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeUniq
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NPlaneValues
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NDual
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.FaceCanonical

@[expose] public section


/-!
# Assembly of Proposition C.5 for `Γ(N)`

Formalized by Claude Sonnet 5.5.

`propC5_gammaN_assembled` proves `PropC5GammaN N n` for every `N ≥ 3`, `n ≥ 4`, composing only declarations that exist:

* the level descent `propC5_of_face_obligations_at_level` (`LevelChangeUniq`: Proposition C.5 at `Γ(N)` from the obligations at a common level `M`,
  `N ∣ M`, `6 ∣ M`; uniqueness descends by `uniqLevel_of_dvd`);
* Eisenstein existence `eisensteinP_gammaN` at `N` and at `M` (`FormClassK/GammaNPlaneValues`);
* dual Eisenstein classes `dualEisenstein_gammaN` at `M` (`FormClassK/GammaNDual`: `Hd`, `dualRQ`, `dualRP`, `QDi`, `PDmod`);
* the perfect canonical face pairing `pairQfaceCan`, `pairQfaceCan_perfect` of the line faces (`GammaNParabolicPD/FaceCanonical`).

The two hypotheses of `C5LevelInputs`, each a statement of real mathematical content, not a tautology:

* `QDiAlignment M n`: linear isomorphisms `𝒞_Q(E^∨) = QDi M n i ≃ QDiLit M n i` between the cuspidal group of the dual Eisenstein series
 and the cuspidal group of the literal Levi module `H¹(N_{Q'_i}, E_n^*)` on which the perfect pairing is defined.
* `StokesAtLevel M n A`: the Stokes relation `⟨ξ_P, r_P c'⟩ + ⟨ξ_Q, r_Q c'⟩ = 0` at level `Γ(M)`, `6 ∣ M`, for the canonical
  line pairings `pairQfaceCan` transported along the alignment `A` and SOME plane pairing `pairP`.  It is the conjunction of (i) the Stokes lemma at `Γ(6)`
  (`gamma6_stokes_of_zeroFlags`, `gamma6_stokes_dualSeries`) applied to the induced module `Ind_{Γ(M)}^{Γ(6)} E_n` (`LevelChangeShapiro/Mackey/Dual`:
  `PhiH_bijective`, `res_decomp`, `phi_qRep`, `dualHom_bijective`), (ii) the orthogonality of the orbit components `lineFacePairM_orth`, and
  (iii) the identification of each orbit component of the cone pairing with the canonical pairing (`pairQfaceCan`, `pairPfaceCan`).
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD

section Open

variable (M n : ℕ) [NeZero M]

/-- **The alignment of the dual cuspidal groups.**  For every line face `i` of level `M`, a linear isomorphism between the cuspidal group
`𝒞_Q(E^∨) = QDi M n i` of the dual Eisenstein series (S7's `dualCuspidalQ`) and the cuspidal group `QDiLit M n i` of the literal Levi module `H¹(N_{Q'_i}, E_n^*)`
on which the perfect canonical pairing `pairQfaceCan` lives. -/
structure QDiAlignment where
  /-- The isomorphism at the line face `i`. -/
  eQ : ∀ i : LineFaces M, QDi M n i ≃ₗ[ℂ] QDiLit M n i

variable {M n}

/-- The canonical line-face pairing of S2 transported along the alignment `A`: `𝒞_{Q'_i}(E_n) × QDi M n i → ℂ`. -/
def QDiAlignment.pairQ (A : QDiAlignment M n) (hM : 3 ≤ M) (i : LineFaces M) :
    lineFaceCuspidal M i.rep n →ₗ[ℂ] QDi M n i →ₗ[ℂ] ℂ :=
  (pairQfaceCan n hM i).compl₂ (A.eQ i).toLinearMap

theorem QDiAlignment.pairQ_perfect (A : QDiAlignment M n) (hM : 3 ≤ M) (i : LineFaces M)
    (a : lineFaceCuspidal M i.rep n) (h : ∀ b, A.pairQ hM i a b = 0) : a = 0 := by
  refine (pairQfaceCan_perfect n hM i).1 a fun y => ?_
  have := h ((A.eQ i).symm y)
  simpa [QDiAlignment.pairQ] using this

/-- Stokes at level `Γ(M)`, `6 ∣ M`.**  There is a plane pairing `pairP : 𝒞_P(E) × (plane restrictions of dual classes) → ℂ` such that for every
global class `c` of `Γ(M)` with zero flag restrictions, all boundary data `ξ_P`, `ξ_Q` of `c`, and every dual Eisenstein class `c' ∈ Hd`,
`⟨ξ_P, r_P c'⟩_P + ∑_i ⟨ξ_{Q,i}, r_{Q,i} c'⟩_{Q_i} = 0` for the canonical line pairings transported along the alignment `A`.  This is the field `stokes` of
`GammaNC5FaceObligations` for the data of S7 (`Hd`, `dualRP`, `dualRQ`) and S2 (`pairQfaceCan`). -/
def StokesAtLevel (hM : 3 ≤ M) (hn : 4 ≤ n) (A : QDiAlignment M n) : Prop :=
  ∃ pairP : PlaneCuspSum M n →ₗ[ℂ] PDmod M n →ₗ[ℂ] ℂ,
    ∀ c : groupCohomology.H2 (gammaNRepAll M n), ZeroFlags M n c →
      ∀ (ξP : PlaneCuspSum M n) (ξQ : LineCuspSum M n),
        planeCuspSumEmbedding M n ξP = planeBoundary M n c →
        lineCuspSumEmbedding M n ξQ = lineBoundary M n c →
        ∀ c' : Hd (N := M) (n := n) hn,
          pairP ξP (dualRP hn c') + sumPairing _ _ (A.pairQ hM) ξQ (dualRQ hM hn c') = 0

/-- **The inputs of Proposition C.5 for `Γ(N)`**: the alignment of the dual cuspidal groups and Stokes at the common level `M`. -/
structure C5LevelInputs (hM : 3 ≤ M) (hn : 4 ≤ n) where
  /-- The alignment `QDi ≃ QDiLit`. -/
  align : QDiAlignment M n
  /-- Stokes at level `M` for the aligned canonical pairings. -/
  stokes : StokesAtLevel hM hn align

end Open

section Assembly

variable {N M n : ℕ} [NeZero N] [NeZero M]

/-- The per-face obligations at level `M` assembled from existing results and the inputs. -/
def faceObligations (hM : 3 ≤ M) (hn : 4 ≤ n) (I : C5LevelInputs hM hn) :
    GammaNC5FaceObligations M n (QDi M n) (PDmod M n) (Hd (N := M) (n := n) hn) := by
  obtain ⟨T, hT⟩ := Classical.indefiniteDescription _ (eisensteinP_gammaN (N := M) (n := n) hM hn)
  obtain ⟨Td, hTd⟩ := Classical.indefiniteDescription _ (dualEisenstein_gammaN (N := M) (n := n) hM hn)
  obtain ⟨pairP, hP⟩ := Classical.indefiniteDescription _ I.stokes
  exact
    { T := T
      eisensteinP := hT
      Td := Td
      rPd := dualRP hn
      rQd := dualRQ hM hn
      pairP := pairP
      pairQface := I.align.pairQ hM
      dualEisenstein := hTd
      stokes := hP
      perfectQface := I.align.pairQ_perfect hM }

/-- **Proposition C.5 for `Γ(N)`, assembled** (`3 ≤ N`, `4 ≤ n`): from the existing results (Eisenstein existence at `N`, level descent from a common level `M` with
`N ∣ M`, `3 ≤ M`) and the two inputs `C5LevelInputs` at level `M` (alignment of the dual cuspidal groups, Stokes at `Γ(M)`; `6 ∣ M` is where Stokes is
expected to be proved). -/
theorem propC5_gammaN_assembled (hN : 3 ≤ N) (hn : 4 ≤ n) (hNM : N ∣ M) (hM : 3 ≤ M) (I : C5LevelInputs hM hn) :
    PropC5GammaN N n :=
  propC5_of_face_obligations_at_level n hNM hM (faceObligations hM hn I) (eisensteinP_gammaN (N := N) (n := n) hN hn)

instance lcmNeZero (N : ℕ) [NeZero N] : NeZero (Nat.lcm N 6) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by norm_num)⟩

theorem three_le_lcm {N : ℕ} [NeZero N] (hN : 3 ≤ N) : 3 ≤ Nat.lcm N 6 :=
  hN.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) (Nat.dvd_lcm_left N 6))

/-- **Proposition C.5 for every `Γ(N)`, `N ≥ 3`, `n ≥ 4`**, with the common level `M = lcm(N, 6)`: it remains to supply `C5LevelInputs` at that level. -/
theorem propC5_gammaN_assembled_lcm (hN : 3 ≤ N) (hn : 4 ≤ n) (I : C5LevelInputs (three_le_lcm hN) hn) :
    PropC5GammaN N n :=
  propC5_gammaN_assembled hN hn (Nat.dvd_lcm_left N 6) (three_le_lcm hN) I

end Assembly

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
