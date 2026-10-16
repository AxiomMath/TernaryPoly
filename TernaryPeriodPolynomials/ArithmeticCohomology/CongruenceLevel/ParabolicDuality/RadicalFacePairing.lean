module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalFaceDet
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.C5Wiring

@[expose] public section


/-!
# The face pairing for the literal contragredient `H¹(N_R, E_n^*)`

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`, ("the
two-generator Koszul complex for the radical pairs degree one with degree one", with the dual local system `E_n^*`).

`cuspidal_literal_pairing`: for a split extension `ℤ² → E → Γ(N)` whose Levi acts on the radical with determinant one, the
Levi-invariant Koszul pairing `radPairingOf : H¹(N_R, E) × H¹(N_R, E^*) → ℂ` (perfect, `RadicalCocycles`/`RadicalLevi`) feeds the
Farey pairing of cuspidal groups (`cuspidal_pairing_gammaN`), so that `𝒞(H¹(N_R, E))` and `𝒞(H¹(N_R, E^*))` are perfectly paired
where `E^*` is the LITERAL contragredient (`dualRepG`) of the coefficient module, not the contragredient of the Levi module.
Instances: `lineFace_literal_pairing`, `planeFace_literal_pairing` (all conjugate faces, determinant lemmas of `RadicalFaceDet`),
and the wiring `QDiLit`, `pairQfaceLit`, `perfectQfaceLit`, `GammaNC5FaceObligations.ofRestLit` replacing the contragredient of
the Levi module (`C5Wiring.QDiDual`) by the Levi module of the contragredient.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open CongruenceSubgroup
open scoped Classical MatrixGroups DirectSum

section Abstract

theorem perfectInv_dual {G : Type} [Group G] (V : Rep ℂ G) [FiniteDimensional ℂ V] :
    PerfectInv (V := V) (W := dualRepG V) (Module.Dual.eval ℂ V) where
  inv γ v φ := by
    change ((dualRepG V).ρ γ φ) (V.ρ γ v) = φ v
    rw [dualRepG_inv]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  left v hv := (Module.forall_dual_apply_eq_zero_iff ℂ v).mp hv
  right φ hφ := by
    ext v
    simpa using hφ v

variable {N : ℕ}

/-- **The perfect pairing of the cuspidal groups `𝒞(H¹(N_R, E)) × 𝒞(H¹(N_R, E^*))` for the literal contragredient `E^*`**:
for a split extension `ℤ² → E → Γ(N)` whose Levi acts on the radical with determinant one, the Levi-invariant Koszul pairing
`H¹(N_R, E) × H¹(N_R, E^*) → ℂ` makes the cuspidal groups of the two Levi modules perfectly dual. -/
theorem cuspidal_literal_pairing (hN : 3 ≤ N) {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
    (s : ext.Splitting) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (rep : Rep ℂ E) [FiniteDimensional ℂ rep] :
    ∃ B : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s rep) →ₗ[ℂ]
        cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG rep)) →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) := by
  have hp := perfectInv_dual rep
  have : FiniteDimensional ℂ (splitRadicalH1Representation s rep) := finiteDimensional_H1 (Rep.res ext.inl rep)
  have : FiniteDimensional ℂ (splitRadicalH1Representation s (dualRepG rep)) :=
    finiteDimensional_H1 (Rep.res ext.inl (dualRepG rep))
  exact cuspidal_pairing_gammaN hN (splitRadicalH1Representation s rep) (splitRadicalH1Representation s (dualRepG rep))
    (radPairingOf (ext := ext) hp)
    (fun γ x y => radPairingOf_levi hp s γ (hdet γ) x y)
    (fun x hx => radPairingOf_left hp x hx) (fun y hy => radPairingOf_right hp y hy)

end Abstract

section Faces

open TernaryPeriodPolynomials.Argument.SeedC3S4c (faceCuspidal faceRadH1 faceRep faceSplitting gammaNPAt)

variable (N : ℕ) [NeZero N] (n : ℕ) (h : SL(3, ℤ))

/-- **The literal contragredient** `E_n^*` of the coefficient module, restricted to the line group of the cusp `h⁻¹ Q h`. -/
abbrev lineFaceRepLit : Rep ℂ (gammaNQAt N h) := dualRepG (lineFaceRep N h n)

/-- **The Levi module `H¹(N_{Q'}, E_n^*)`** of the line cusp `Q' = h⁻¹ Q h` for the literal contragredient `E_n^*`. -/
abbrev lineFaceRadH1Lit : Rep ℂ (Gamma N) := splitRadicalH1Representation (lineFaceSplitting N h) (lineFaceRepLit N n h)

/-- **The literal contragredient** `E_n^*` of the coefficient module, restricted to the plane group of the cusp `h⁻¹ P h`. -/
abbrev faceRepLit : Rep ℂ (gammaNPAt N h) := dualRepG (faceRep N h n)

/-- **The Levi module `H¹(N_{P'}, E_n^*)`** of the plane cusp `P' = h⁻¹ P h` for the literal contragredient `E_n^*`. -/
abbrev faceRadH1Lit : Rep ℂ (Gamma N) := splitRadicalH1Representation (faceSplitting N h) (faceRepLit N n h)

variable {N}

/-- **Perfect pairing `𝒞_{Q'}(E_n) × 𝒞(H¹(N_{Q'}, E_n^*)) → ℂ` for the literal contragredient**. -/
theorem lineFace_literal_pairing (hN : 3 ≤ N) :
    ∃ B : lineFaceCuspidal N h n →ₗ[ℂ] cuspidalSubspace (Gamma N) (lineFaceRadH1Lit N n h) →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) :=
  cuspidal_literal_pairing hN (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) (lineFaceRep N h n)

/-- **Perfect pairing `𝒞_{P'}(E_n) × 𝒞(H¹(N_{P'}, E_n^*)) → ℂ` for the literal contragredient**. -/
theorem planeFace_literal_pairing (hN : 3 ≤ N) :
    ∃ B : faceCuspidal N h n →ₗ[ℂ] cuspidalSubspace (Gamma N) (faceRadH1Lit N n h) →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) :=
  cuspidal_literal_pairing hN (faceSplitting N h) (planeFaceRadicalInput_det N h) (faceRep N h n)

end Faces

section Wiring

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- `QDi i`: the cuspidal group of the Levi module `H¹(N_{Q'_i}, E_n^*)` for the literal contragredient `E_n^*`. -/
abbrev QDiLit (i : LineFaces N) : Type := cuspidalSubspace (Gamma N) (lineFaceRadH1Lit N n i.rep)

variable {N} (hN : 3 ≤ N)

/-- **The pairing `⟨ , ⟩_Q` of the line face `i` with the cuspidal group of `H¹(N_{Q'_i}, E_n^*)`** (field `pairQface`). -/
def pairQfaceLit (i : LineFaces N) : lineFaceCuspidal N i.rep n →ₗ[ℂ] QDiLit N n i →ₗ[ℂ] ℂ :=
  Classical.choose (lineFace_literal_pairing n i.rep hN)

/-- **Perfectness of the line-face pairing (left)** (field `perfectQface`). -/
theorem perfectQfaceLit (i : LineFaces N) (a : lineFaceCuspidal N i.rep n) (h : ∀ b, pairQfaceLit n hN i a b = 0) :
    a = 0 :=
  (Classical.choose_spec (lineFace_literal_pairing n i.rep hN)).1 a h

theorem perfectQfaceLit_right (i : LineFaces N) (b : QDiLit N n i) (h : ∀ a, pairQfaceLit n hN i a b = 0) :
    b = 0 :=
  (Classical.choose_spec (lineFace_literal_pairing n i.rep hN)).2 b h

/-- **`GammaNC5FaceObligations` with the line-face pairing instantiated for the literal contragredient**: the dual module of the
line face `i` is the cuspidal group of `H¹(N_{Q'_i}, E_n^*)` and the pairing is the Levi-invariant Koszul pairing
`H¹(N_{Q'_i}, E_n) × H¹(N_{Q'_i}, E_n^*) → ℂ` of the radical lattice, made perfect on cuspidal groups by the Farey model. -/
def GammaNC5FaceObligations.ofRestLit {PD Hd : Type} [AddCommGroup PD] [Module ℂ PD] [AddCommGroup Hd] [Module ℂ Hd]
    (T : PlaneCuspSum N n →ₗ[ℂ] LineCuspSum N n)
    (eisensteinP : ∀ ξ : PlaneCuspSum N n, ∃ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c ∧
      planeCuspSumEmbedding N n ξ = planeBoundary N n c ∧ lineCuspSumEmbedding N n (T ξ) = lineBoundary N n c)
    (Td : (⨁ i, QDiLit N n i) →ₗ[ℂ] PD) (rPd : Hd →ₗ[ℂ] PD) (rQd : Hd →ₗ[ℂ] (⨁ i, QDiLit N n i))
    (pairP : PlaneCuspSum N n →ₗ[ℂ] PD →ₗ[ℂ] ℂ)
    (dualEisenstein : ∀ η : ⨁ i, QDiLit N n i, ∃ c' : Hd, rQd c' = η ∧ rPd c' = Td η)
    (stokes : ∀ c : groupCohomology.H2 (gammaNRepAll N n), ZeroFlags N n c →
      ∀ (ξP : PlaneCuspSum N n) (ξQ : LineCuspSum N n),
        planeCuspSumEmbedding N n ξP = planeBoundary N n c →
        lineCuspSumEmbedding N n ξQ = lineBoundary N n c →
        ∀ c' : Hd, pairP ξP (rPd c') + sumPairing _ _ (pairQfaceLit n hN) ξQ (rQd c') = 0) :
    GammaNC5FaceObligations N n (QDiLit N n) PD Hd where
  T := T
  eisensteinP := eisensteinP
  Td := Td
  rPd := rPd
  rQd := rQd
  pairP := pairP
  pairQface := pairQfaceLit n hN
  dualEisenstein := dualEisenstein
  stokes := stokes
  perfectQface := perfectQfaceLit n hN

end Wiring

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
