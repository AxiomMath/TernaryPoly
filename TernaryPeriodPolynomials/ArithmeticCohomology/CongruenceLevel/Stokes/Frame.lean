module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.C5Reduction

@[expose] public section


/-!
# Lemma `ar:lem:stokes` at level `Γ(N)`: the boundary frame and the Stokes relation for the face pairings

Formalized by Claude Sonnet 5.5.

The proof of the paper has three steps, each a field of `BoundaryFrame`: (1) geometric Stokes for the degree-four cup product of two
global classes on the oriented boundary; (2) the mapping-cone decomposition of the restriction of a class with zero flag restrictions into the
compactly supported lifts of its face restrictions plus a corner class; (3) orthogonality of different faces and of corner classes to the face lifts
(cutoff near the flag collars, no triple intersections in rank three).  `BoundaryFrame.stokes` is the algebra deducing
`⟨r_P a, r_P b⟩_P + ∑_{line faces} ⟨r_Q a, r_Q b⟩_Q = 0` from them, with the face pairings *defined* as the boundary pairings of the face lifts
(`pairP`, `pairQface`); `stokes_of_comparison` transfers the relation to any face pairings equal to those (the Hochschild-Serre/parabolic
pairings of the parabolic-duality construction, via the comparison `hP`, `hQ`); `toFaceObligations` plugs a frame into
`GammaNC5FaceObligations`.

What is NOT here: an instance of `BoundaryFrame` for any `Γ(N)`.
-/

open scoped MatrixGroups DirectSum

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **The boundary frame of Lemma `ar:lem:stokes` at level `Γ(N)`**: the Poincaré-duality pairing `β` of the boundary
`∂X̄_Γ`, the restriction maps of global classes to the boundary, and the extension-by-zero maps of the face classes (compactly supported
lifts).  The fields are the steps of the paper's proof:

* `geoStokes`: the integral of the restriction of a degree-four cup product over the oriented boundary vanishes (Stokes);
* `decomp`: a global class with zero flag restrictions and face restrictions `(ξ_P, ξ_Q)` restricts, on the boundary, to the sum of the face lifts
  of `ξ_P` and `ξ_Q` plus a corner class (the mapping-cone coordinate of the paper), `K` being the corner classes; likewise for dual classes;
* `orth`: different faces and corner classes are orthogonal (the face representatives vanish on a collar of the flags, and distinct flag collars are
  disjoint; no triple intersections in rank three).

`PD`, `QDi` are the dual mixed cuspidal groups and `Hd` the admissible dual global classes. -/
structure BoundaryFrame (QDi : LineFaces N → Type) [∀ i, AddCommGroup (QDi i)] [∀ i, Module ℂ (QDi i)]
    (PD Hd : Type) [AddCommGroup PD] [Module ℂ PD] [AddCommGroup Hd] [Module ℂ Hd] where
  Bd : Type
  Bd' : Type
  [instBd : AddCommGroup Bd]
  [instBdM : Module ℂ Bd]
  [instBd' : AddCommGroup Bd']
  [instBdM' : Module ℂ Bd']
  β : Bd →ₗ[ℂ] Bd' →ₗ[ℂ] ℂ
  rb : groupCohomology.H2 (gammaNRepAll N n) →ₗ[ℂ] Bd
  rPd : Hd →ₗ[ℂ] PD
  rQd : Hd →ₗ[ℂ] (⨁ i, QDi i)
  rbd : Hd →ₗ[ℂ] Bd'
  liftP : PlaneCuspSum N n →ₗ[ℂ] Bd
  liftP' : PD →ₗ[ℂ] Bd'
  liftQ : ∀ i : LineFaces N, lineFaceCuspidal N i.rep n →ₗ[ℂ] Bd
  liftQ' : ∀ i : LineFaces N, QDi i →ₗ[ℂ] Bd'
  K : Submodule ℂ Bd
  K' : Submodule ℂ Bd'
  geoStokes : ∀ (c : groupCohomology.H2 (gammaNRepAll N n)) (c' : Hd), β (rb c) (rbd c') = 0
  decomp : ∀ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c →
    ∀ (ξP : PlaneCuspSum N n) (ξQ : LineCuspSum N n),
      planeCuspSumEmbedding N n ξP = planeBoundary N n c →
      lineCuspSumEmbedding N n ξQ = lineBoundary N n c →
      rb c - liftP ξP - DirectSum.toModule ℂ (LineFaces N) Bd liftQ ξQ ∈ K
  decomp' : ∀ c' : Hd, rbd c' - liftP' (rPd c') - DirectSum.toModule ℂ (LineFaces N) Bd' liftQ' (rQd c') ∈ K'
  orthPQ : ∀ (ξ : PlaneCuspSum N n) (η : ⨁ i, QDi i), β (liftP ξ) (DirectSum.toModule ℂ _ _ liftQ' η) = 0
  orthQP : ∀ (ξ : LineCuspSum N n) (η : PD), β (DirectSum.toModule ℂ _ _ liftQ ξ) (liftP' η) = 0
  orthQQ : ∀ (i j : LineFaces N) (a : lineFaceCuspidal N i.rep n) (b : QDi j), i ≠ j → β (liftQ i a) (liftQ' j b) = 0
  orthK : ∀ (k : Bd), k ∈ K → ∀ (k' : Bd'), k' ∈ K' → β k k' = 0
  orthKF : ∀ (k : Bd), k ∈ K → ∀ (η : PD) (η' : ⨁ i, QDi i),
    β k (liftP' η + DirectSum.toModule ℂ _ _ liftQ' η') = 0
  orthFK : ∀ (ξ : PlaneCuspSum N n) (ξ' : LineCuspSum N n) (k' : Bd'), k' ∈ K' →
    β (liftP ξ + DirectSum.toModule ℂ _ _ liftQ ξ') k' = 0

attribute [instance] BoundaryFrame.instBd BoundaryFrame.instBdM BoundaryFrame.instBd' BoundaryFrame.instBdM'

namespace BoundaryFrame

variable {N n} {QDi : LineFaces N → Type} [∀ i, AddCommGroup (QDi i)] [∀ i, Module ℂ (QDi i)]
  {PD Hd : Type} [AddCommGroup PD] [Module ℂ PD] [AddCommGroup Hd] [Module ℂ Hd]
  (F : BoundaryFrame N n QDi PD Hd)

/-- The plane face pairing induced by the boundary pairing: the pairing of the face lifts. -/
def pairP : PlaneCuspSum N n →ₗ[ℂ] PD →ₗ[ℂ] ℂ := (F.β.comp F.liftP).compl₂ F.liftP'

/-- The per-face line pairing induced by the boundary pairing. -/
def pairQface (i : LineFaces N) : lineFaceCuspidal N i.rep n →ₗ[ℂ] QDi i →ₗ[ℂ] ℂ :=
  (F.β.comp (F.liftQ i)).compl₂ (F.liftQ' i)

theorem toModule_eq_sum {M : Type} [AddCommGroup M] [Module ℂ M] {B : LineFaces N → Type}
    [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (φ : ∀ i, B i →ₗ[ℂ] M) (x : ⨁ i, B i) :
    DirectSum.toModule ℂ (LineFaces N) M φ x = ∑ i, φ i (x i) := by
  conv_lhs => rw [← DirectSum.sum_univ_of x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← DirectSum.lof_eq_of ℂ, DirectSum.toModule_lof]

/-- **Lemma `ar:lem:stokes` at level `Γ(N)`, from the boundary frame.**  For a global class `a` with zero flag restrictions and face
restrictions `(ξ_P, ξ_Q)` and an admissible dual class `b` with face restrictions `(r_P b, r_Q b)`:
`⟨ξ_P, r_P b⟩_P + ∑_{line faces} ⟨ξ_Q, r_Q b⟩_Q = 0`. -/
theorem stokes (c : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c)
    (ξP : PlaneCuspSum N n) (ξQ : LineCuspSum N n)
    (hP : planeCuspSumEmbedding N n ξP = planeBoundary N n c)
    (hQ : lineCuspSumEmbedding N n ξQ = lineBoundary N n c) (c' : Hd) :
    F.pairP ξP (F.rPd c') + sumPairing _ _ F.pairQface ξQ (F.rQd c') = 0 := by
  set A := F.liftP ξP
  set Q := DirectSum.toModule ℂ (LineFaces N) F.Bd F.liftQ ξQ
  set B := F.liftP' (F.rPd c')
  set Q' := DirectSum.toModule ℂ (LineFaces N) F.Bd' F.liftQ' (F.rQd c')
  obtain ⟨k, hk, hkc⟩ : ∃ k ∈ F.K, F.rb c = A + Q + k :=
    ⟨F.rb c - A - Q, F.decomp c hz ξP ξQ hP hQ, by abel⟩
  obtain ⟨k', hk', hkc'⟩ : ∃ k' ∈ F.K', F.rbd c' = B + Q' + k' :=
    ⟨F.rbd c' - B - Q', F.decomp' c', by abel⟩
  have h0 := F.geoStokes c c'
  rw [hkc, hkc'] at h0
  have e1 := F.orthFK ξP ξQ k' hk'
  have e2 := F.orthKF k hk (F.rPd c') (F.rQd c')
  have e3 := F.orthK k hk k' hk'
  have e4 := F.orthPQ ξP (F.rQd c')
  have e5 := F.orthQP ξQ (F.rPd c')
  have hQQ : F.β Q Q' = sumPairing _ _ F.pairQface ξQ (F.rQd c') := by
    rw [sumPairing_apply]
    simp only [Q, Q']
    rw [toModule_eq_sum, toModule_eq_sum]
    simp only [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rfl
    · intro j _ hj
      exact F.orthQQ j i (ξQ j) (F.rQd c' i) hj
    · simp
  have hexp : F.β (A + Q + k) (B + Q' + k') =
      F.β A B + F.β Q Q' + (F.β (A + Q) k' + F.β k (B + Q') + F.β k k' + F.β A Q' + F.β Q B) := by
    simp only [map_add, LinearMap.add_apply]
    abel
  rw [hexp, e1, e2, e3, e4, e5, hQQ] at h0
  simpa [pairP] using h0

/-- **Stokes for given face pairings**: if the face pairings supplied by the Hochschild-Serre/parabolic-duality construction
(`pairP'`, `pairQ'`) agree with the pairings of the face lifts in the boundary (`hP`, `hQ`: the comparison of the algebraic face pairing with the
integral of the cup product over the oriented face), they satisfy the Stokes relation. -/
theorem stokes_of_comparison (pairP' : PlaneCuspSum N n →ₗ[ℂ] PD →ₗ[ℂ] ℂ)
    (pairQ' : ∀ i : LineFaces N, lineFaceCuspidal N i.rep n →ₗ[ℂ] QDi i →ₗ[ℂ] ℂ)
    (hP : pairP' = F.pairP) (hQ : pairQ' = F.pairQface) :
    ∀ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c →
      ∀ (ξP : PlaneCuspSum N n) (ξQ : LineCuspSum N n),
        planeCuspSumEmbedding N n ξP = planeBoundary N n c →
        lineCuspSumEmbedding N n ξQ = lineBoundary N n c →
        ∀ c' : Hd, pairP' ξP (F.rPd c') + sumPairing _ _ pairQ' ξQ (F.rQd c') = 0 := by
  subst hP hQ
  exact fun c hz ξP ξQ hP hQ c' => F.stokes c hz ξP ξQ hP hQ c'

/-- The per-face obligations of `GammaNC5FaceObligations` assembled from a boundary frame (which supplies the Stokes field and the pairings) and
the analytic inputs: the Eisenstein classes, and the perfectness of the face pairings of the frame. -/
def toFaceObligations (T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n)
    (eisensteinP : ∀ ξ : PlaneCuspSum N n, ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
      planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧
        lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c)
    (Td : (⨁ i, QDi i) →ₗ[ℂ] PD)
    (dualEisenstein : ∀ η : ⨁ i, QDi i, ∃ c' : Hd, F.rQd c' = η ∧ F.rPd c' = Td η)
    (perfectQface : ∀ (i : LineFaces N) (a : lineFaceCuspidal N i.rep n),
      (∀ b, F.pairQface i a b = 0) → a = 0) :
    GammaNC5FaceObligations N n QDi PD Hd where
  T := T
  eisensteinP := eisensteinP
  Td := Td
  rPd := F.rPd
  rQd := F.rQd
  pairP := F.pairP
  pairQface := F.pairQface
  dualEisenstein := dualEisenstein
  stokes := fun c hz ξP ξQ hP hQ c' => F.stokes c hz ξP ξQ hP hQ c'
  perfectQface := perfectQface

end BoundaryFrame

end TernaryPeriodPolynomials.Argument.GammaNStokes
