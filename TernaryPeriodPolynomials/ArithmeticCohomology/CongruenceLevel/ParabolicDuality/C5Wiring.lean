module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.FacePairingBase
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.C5Reduction

@[expose] public section


/-!
# Instantiating the line-face pairing fields of `GammaNC5FaceObligations`

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`; reduction of Proposition C.5
at level `Γ(N)`: the `GammaNFacesFull.GammaNC5FaceObligations`.

`QDiDual N n i` is the cuspidal group of the contragredient of the Levi module `H¹(N_{Q'_i}, E_n)` of the line face `i`;
`pairQfaceDual` is the perfect pairing `lineFaceCuspidal × QDiDual → ℂ` constructed from the Farey model (`lineFace_cuspidal_dual_pairing`)
and `perfectQfaceDual` its nondegeneracy, i.e. the fields `pairQface` and `perfectQface` of `GammaNC5FaceObligations`, as data.
`GammaNC5FaceObligations.ofRest` assembles the structure from the remaining fields.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open CongruenceSubgroup
open scoped Classical MatrixGroups DirectSum

section Wiring

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- The contragredient of the Levi module `H¹(N_{Q'}, E_n)` of the line face `i`. -/
abbrev lineFaceDualMod (i : LineFaces N) : Rep ℂ (Gamma N) := dualRepG (lineFaceRadH1 N i.rep n)

/-- `QDi i`: the cuspidal group of the contragredient Levi module of the line face `i`. -/
abbrev QDiDual (i : LineFaces N) : Type := cuspidalSubspace (Gamma N) (lineFaceDualMod N n i)

variable {N} (hN : 3 ≤ N)

/-- **The pairing `⟨ , ⟩_Q` of the line face `i` with the cuspidal group of the contragredient** (field `pairQface`). -/
def pairQfaceDual (i : LineFaces N) : lineFaceCuspidal N i.rep n →ₗ[ℂ] QDiDual N n i →ₗ[ℂ] ℂ :=
  Classical.choose (lineFace_cuspidal_dual_pairing n i.rep hN)

/-- **Perfectness of the line-face pairing** (field `perfectQface`). -/
theorem perfectQfaceDual (i : LineFaces N) (a : lineFaceCuspidal N i.rep n) (h : ∀ b, pairQfaceDual n hN i a b = 0) :
    a = 0 :=
  (Classical.choose_spec (lineFace_cuspidal_dual_pairing n i.rep hN)).1 a h

theorem perfectQfaceDual_right (i : LineFaces N) (b : QDiDual N n i) (h : ∀ a, pairQfaceDual n hN i a b = 0) :
    b = 0 :=
  (Classical.choose_spec (lineFace_cuspidal_dual_pairing n i.rep hN)).2 b h

/-- **`GammaNC5FaceObligations` with the line-face pairing instantiated**: the structure is assembled from the remaining fields
(the Eisenstein classes, the dual classes, the plane pairing and the Stokes identity, stated for `pairQfaceDual`), and the
perfectness of the line pairing is supplied by the Farey/Poincaré-Lefschetz model for `Γ(N)`. -/
def GammaNC5FaceObligations.ofRest {PD Hd : Type} [AddCommGroup PD] [Module ℂ PD] [AddCommGroup Hd] [Module ℂ Hd]
    (T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n)
    (eisensteinP : ∀ ξ : PlaneCuspSum N n, ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
      planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧ lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c)
    (Td : (⨁ i, QDiDual N n i) →ₗ[ℂ] PD) (rPd : Hd →ₗ[ℂ] PD) (rQd : Hd →ₗ[ℂ] (⨁ i, QDiDual N n i))
    (pairP : PlaneCuspSum N n →ₗ[ℂ] PD →ₗ[ℂ] ℂ)
    (dualEisenstein : ∀ η : ⨁ i, QDiDual N n i, ∃ c' : Hd, rQd c' = η ∧ rPd c' = Td η)
    (stokes : ∀ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c →
      ∀ (ξP : PlaneCuspSum N n) (ξQ : LineCuspSum N n),
        planeCuspSumEmbedding N n ξP = planeBoundary N n c →
        lineCuspSumEmbedding N n ξQ = lineBoundary N n c →
        ∀ c' : Hd, pairP ξP (rPd c') + sumPairing _ _ (pairQfaceDual n hN) ξQ (rQd c') = 0) :
    GammaNC5FaceObligations N n (QDiDual N n) PD Hd where
  T := T
  eisensteinP := eisensteinP
  Td := Td
  rPd := rPd
  rQd := rQd
  pairP := pairP
  pairQface := pairQfaceDual n hN
  dualEisenstein := dualEisenstein
  stokes := stokes
  perfectQface := perfectQfaceDual n hN

end Wiring

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
