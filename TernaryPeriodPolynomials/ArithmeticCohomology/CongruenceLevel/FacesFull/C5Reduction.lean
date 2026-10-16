module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.PropC5GammaN
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinClass

@[expose] public section


/-!
# Proposition C.5 at level `Γ(N)`: identification of the coefficient modules and the per-face form of the pairing obligations

Formalized by Claude Sonnet 5.5.

* `gammaRep_gammaN_eq`: the complex coefficient module `gammaRep (gammaN N) n` of the form-series construction is **definitionally** the module
  `gammaNRepAll N n` of the restrictions `rLine`, `rPlane`, `rFlag`; `eisensteinGlobalClass` is the Eisenstein class of `Γ(N)` as an element of
  the cohomology group on which these restrictions act (the field `eisensteinP` of `GammaNC5Obligations` is a statement about it);
* `sumPairing`, `sumPairing_left_nondegenerate`: the orthogonal sum of per-face pairings on the direct sum over the faces, nondegenerate as soon as every
  summand is;
* `GammaNC5FaceObligations`, `propC5_gammaN_of_face_obligations`: `GammaNC5Obligations` with the line pairing given face by face, so that field 4
  (perfectness) is a per-face statement (Poincaré duality for the modular curve of level `N`) and only Stokes (field 3) remains global.
-/

open scoped MatrixGroups DirectSum

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNFacesFull

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.GammaNFaces

section Identify

variable (N : ℕ) [NeZero N] (n : ℕ)

omit [NeZero N] in
/-- **Identification of the coefficient modules.**  The complex coefficient module `gammaRep (gammaN N) n` of the form-series
construction (`Proofs/EisensteinClass`) is, definitionally, the coefficient module `gammaNRepAll N n` of the face and flag restrictions of
this development: both are `E_n` pulled back through `Γ(N) ↪ SL₃(ℤ) → GL₃(ℝ)`. -/
theorem gammaRep_gammaN_eq :
    TernaryPeriodPolynomials.Argument.EisensteinClass.gammaRep (gammaN N) n = gammaNRepAll N n := rfl

/-- The complexified class of the Eisenstein series `𝓔_P(ω_h)` of `Γ(N)`, as a global class in the
cohomology group on which `rLine`, `rPlane`, `rFlag` act. -/
def eisensteinGlobalClass (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) :
    groupCohomology.H2 (gammaNRepAll N n) :=
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass.eisensteinClassC_gammaN N n f hn

end Identify

section Sum

variable {ι : Type} [Fintype ι] (A B : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]

/-- The orthogonal sum of per-face pairings on the direct sums over the faces. -/
def sumPairing (p : ∀ i, A i →ₗ[ℂ] B i →ₗ[ℂ] ℂ) : (⨁ i, A i) →ₗ[ℂ] (⨁ i, B i) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x y => ∑ i, p i (x i) (y i))
    (fun x x' y => by simp [Finset.sum_add_distrib])
    (fun c x y => by simp [DirectSum.smul_apply, Finset.mul_sum])
    (fun x y y' => by simp [Finset.sum_add_distrib])
    (fun c x y => by simp [DirectSum.smul_apply, Finset.mul_sum])

theorem sumPairing_apply (p : ∀ i, A i →ₗ[ℂ] B i →ₗ[ℂ] ℂ) (x : ⨁ i, A i) (y : ⨁ i, B i) :
    sumPairing A B p x y = ∑ i, p i (x i) (y i) := rfl

/-- **A sum of pairings is nondegenerate in the first argument iff each one is** (the faces are orthogonal): reduces the perfectness of the
face pairing of `Γ(N)` to a per-face statement. -/
theorem sumPairing_left_nondegenerate (p : ∀ i, A i →ₗ[ℂ] B i →ₗ[ℂ] ℂ)
    (h : ∀ i (a : A i), (∀ b, p i a b = 0) → a = 0) :
    ∀ x : ⨁ i, A i, (∀ y, sumPairing A B p x y = 0) → x = 0 := by
  intro x hx
  ext i
  apply h i
  intro b
  have := hx (DirectSum.of B i b)
  rw [sumPairing_apply, Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hj
    rw [DirectSum.of_eq_of_ne i j b hj, map_zero]
  · simp

end Sum

section Faces

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **The obligations of `GammaNC5Obligations` with the line pairing given face by face.**  `QDi i` is the dual mixed cuspidal group
`𝒞_{Q'}(E*)` of the line face `i`, `pairQface i` the per-face pairing (Koszul pairing on the torus fibre composed with the parabolic cup
pairing of the Levi `Γ₂(N)`), and `perfectQface i` its nondegeneracy in the first argument (Poincaré duality for the
modular curve of level `N` with coefficients `H¹(N_{Q'}, E)`); the direct sum of the per-face pairings is `sumPairing`. -/
structure GammaNC5FaceObligations (QDi : LineFaces N → Type) [∀ i, AddCommGroup (QDi i)] [∀ i, Module ℂ (QDi i)]
    (PD Hd : Type) [AddCommGroup PD] [Module ℂ PD] [AddCommGroup Hd] [Module ℂ Hd] where
  T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n
  eisensteinP : ∀ ξ : PlaneCuspSum N n, ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
      planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧
        lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c
  Td : (⨁ i, QDi i) →ₗ[ℂ] PD
  rPd : Hd →ₗ[ℂ] PD
  rQd : Hd →ₗ[ℂ] (⨁ i, QDi i)
  pairP : PlaneCuspSum N n →ₗ[ℂ] PD →ₗ[ℂ] ℂ
  pairQface : ∀ i : LineFaces N, lineFaceCuspidal N i.rep n →ₗ[ℂ] QDi i →ₗ[ℂ] ℂ
  dualEisenstein : ∀ η : ⨁ i, QDi i, ∃ c' : Hd, rQd c' = η ∧ rPd c' = Td η
  stokes : ∀ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c →
    ∀ (ξP : PlaneCuspSum N n) (ξQ : LineCuspSum N n),
      planeCuspSumEmbedding N n ξP = planeBoundary N n c →
      lineCuspSumEmbedding N n ξQ = lineBoundary N n c →
      ∀ c' : Hd, pairP ξP (rPd c') + sumPairing _ _ pairQface ξQ (rQd c') = 0
  perfectQface : ∀ (i : LineFaces N) (a : lineFaceCuspidal N i.rep n), (∀ b, pairQface i a b = 0) → a = 0

/-- The per-face obligations give the obligations of `GammaNC5Obligations` (the perfectness of the sum of the face pairings is formal). -/
def GammaNC5FaceObligations.toObligations {QDi : LineFaces N → Type} [∀ i, AddCommGroup (QDi i)]
    [∀ i, Module ℂ (QDi i)] {PD Hd : Type} [AddCommGroup PD] [Module ℂ PD] [AddCommGroup Hd] [Module ℂ Hd]
    (O : GammaNC5FaceObligations N n QDi PD Hd) : GammaNC5Obligations N n PD (⨁ i, QDi i) Hd where
  T := O.T
  eisensteinP := O.eisensteinP
  Td := O.Td
  rPd := O.rPd
  rQd := O.rQd
  pairP := O.pairP
  pairQ := sumPairing _ _ O.pairQface
  dualEisenstein := O.dualEisenstein
  stokes := O.stokes
  perfectQ := sumPairing_left_nondegenerate _ _ O.pairQface O.perfectQface

/-- **Proposition C.5 at level `Γ(N)` from the per-face obligations.** -/
theorem propC5_gammaN_of_face_obligations {QDi : LineFaces N → Type} [∀ i, AddCommGroup (QDi i)]
    [∀ i, Module ℂ (QDi i)] {PD Hd : Type} [AddCommGroup PD] [Module ℂ PD] [AddCommGroup Hd] [Module ℂ Hd]
    (O : GammaNC5FaceObligations N n QDi PD Hd) : PropC5GammaN N n :=
  propC5_gammaN_of_obligations N n O.toObligations

end Faces

end TernaryPeriodPolynomials.Argument.GammaNFacesFull
