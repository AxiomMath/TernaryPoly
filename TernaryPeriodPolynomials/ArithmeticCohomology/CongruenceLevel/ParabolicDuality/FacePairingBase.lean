module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.FiniteH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.LineFaces
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDRadical
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneCusps
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.GammaNCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelOne

@[expose] public section


/-!
# The base pairing of the faces of `Γ(N)`

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

* `cuspidal_dual_pairing`: for every finite-dimensional `Γ(N)`-module `V` (Mathlib's `Γ(N) ≤ SL₂(ℤ)`, `N ≥ 3`) the literal cuspidal group
  `𝒞(V) ⊆ H¹(Γ(N), V)` is perfectly paired with the cuspidal group of the contragredient `V^∨`;
* `lineFace_cuspidal_dual_pairing`, `planeFace_cuspidal_dual_pairing`: this for `V = H¹(N_{Q'}, E_n)` (resp. `H¹(N_{P'}, E_n)`), i.e. for
  the mixed cuspidal groups `𝒞_{Q'}(E_n)` = `lineFaceCuspidal`, `𝒞_{P'}(E_n)` = `faceCuspidal` of every face (the Levi modules are finite
  dimensional, `finiteDimensional_H1`, as `N_R ≅ ℤ²` is finitely generated);
* `gammaNCuspidal_binary_pairing`: for the standard plane cusp, through the binary coordinate `H¹(N_P, E_n) ≅ Sym^{n+1} ⊗ det⁻¹`
  (`gammaNCoordinateIso`), the apolar pairing of binary forms (the pairing whose parabolic cup product is the Petersson-type pairing of the paper) perfectly pairs `𝒞_P(E_n)` with the cuspidal group of `Sym^{n+1}`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open scoped Classical MatrixGroups

section Dual

variable {N : ℕ}

/-- The contragredient representation, as a `Rep`. -/
abbrev dualRepG {G : Type} [Group G] (V : Rep ℂ G) : Rep ℂ G := Rep.of V.ρ.dual

instance {G : Type} [Group G] (V : Rep ℂ G) [FiniteDimensional ℂ V] : FiniteDimensional ℂ (dualRepG V) :=
  inferInstanceAs (FiniteDimensional ℂ (Module.Dual ℂ V))

theorem dualRepG_inv {G : Type} [Group G] (V : Rep ℂ G) (g : G) (v : V) (φ : Module.Dual ℂ V) :
    ((dualRepG V).ρ g φ) v = φ (V.ρ g⁻¹ v) := by
  simp [Representation.dual_apply, Module.Dual.transpose_apply]

/-- **Perfect pairing of the cuspidal groups of a finite-dimensional module and its contragredient.** -/
theorem cuspidal_dual_pairing (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) [FiniteDimensional ℂ V] :
    ∃ B : cuspidalSubspace (Gamma N) V →ₗ[ℂ] cuspidalSubspace (Gamma N) (dualRepG V) →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) := by
  refine cuspidal_pairing_gammaN hN V (dualRepG V) (Module.Dual.eval ℂ V) (fun γ v φ => ?_) ?_ ?_
  · change ((dualRepG V).ρ γ φ) (V.ρ γ v) = φ v
    rw [dualRepG_inv]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · exact fun v hv => (Module.forall_dual_apply_eq_zero_iff ℂ v).mp hv
  · intro φ hφ
    ext v
    simpa using hφ v

end Dual

section Faces

variable (N : ℕ) [NeZero N] (n : ℕ) (h : SL(3, ℤ))

instance lineFaceRep_fd : FiniteDimensional ℂ (TernaryPeriodPolynomials.Argument.GammaNFaces.lineFaceRep N h n) :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.homogeneousPoly_finite n

instance faceRep_fd : FiniteDimensional ℂ (TernaryPeriodPolynomials.Argument.SeedC3S4c.faceRep N h n) :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.homogeneousPoly_finite n

instance lineFaceRadH1_fd :
    FiniteDimensional ℂ (TernaryPeriodPolynomials.Argument.GammaNFaces.lineFaceRadH1 N h n) :=
  finiteDimensional_H1 (Rep.res (TernaryPeriodPolynomials.Argument.GammaNFaces.lineFaceExt N h).inl
    (TernaryPeriodPolynomials.Argument.GammaNFaces.lineFaceRep N h n))

instance faceRadH1_fd :
    FiniteDimensional ℂ (TernaryPeriodPolynomials.Argument.SeedC3S4c.faceRadH1 N h n) :=
  finiteDimensional_H1 (Rep.res (TernaryPeriodPolynomials.Argument.SeedC3S4c.faceExt N h).inl
    (TernaryPeriodPolynomials.Argument.SeedC3S4c.faceRep N h n))

end Faces

section FacePairings

variable {N : ℕ} [NeZero N] (n : ℕ) (h : SL(3, ℤ))

open TernaryPeriodPolynomials.Argument.GammaNFaces (lineFaceCuspidal lineFaceRadH1)
open TernaryPeriodPolynomials.Argument.SeedC3S4c (faceCuspidal faceRadH1)

/-- **The pairing of the line faces** `𝒞_{Q'}(E_n) × 𝒞(H¹(N_{Q'}, E_n)^∨) → ℂ` is perfect (`N ≥ 3`). -/
theorem lineFace_cuspidal_dual_pairing (hN : 3 ≤ N) :
    ∃ B : lineFaceCuspidal N h n →ₗ[ℂ] cuspidalSubspace (Gamma N) (dualRepG (lineFaceRadH1 N h n)) →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) :=
  cuspidal_dual_pairing hN (lineFaceRadH1 N h n)

/-- **The pairing of the plane faces** `𝒞_{P'}(E_n) × 𝒞(H¹(N_{P'}, E_n)^∨) → ℂ` is perfect (`N ≥ 3`). -/
theorem planeFace_cuspidal_dual_pairing (hN : 3 ≤ N) :
    ∃ B : faceCuspidal N h n →ₗ[ℂ] cuspidalSubspace (Gamma N) (dualRepG (faceRadH1 N h n)) →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) :=
  cuspidal_dual_pairing hN (faceRadH1 N h n)

end FacePairings

section Binary

open TernaryPeriodPolynomials.Argument.SeedC3S4c (gammaNCuspidal gammaNCoordinateIso cuspidal_iso_iff binRep)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (modularBinaryRep)
open TernaryPeriodPolynomials.BoundaryDuality

/-- Isomorphic `Λ`-modules have isomorphic cuspidal subspaces. -/
def cuspEquivOfIso {Λ : Subgroup SL(2, ℤ)} {V W : Rep ℂ Λ} (e : V ≅ W) :
    cuspidalSubspace Λ V ≃ₗ[ℂ] cuspidalSubspace Λ W :=
  let E : groupCohomology.H1 V ≃ₗ[ℂ] groupCohomology.H1 W := ((groupCohomology.functor ℂ Λ 1).mapIso e).toLinearEquiv
  LinearEquiv.ofSubmodules E _ _ (by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (cuspidal_iso_iff e x).mp hx
    · intro hz
      refine ⟨E.symm z, ?_, E.apply_symm_apply z⟩
      show E.symm z ∈ cuspidalSubspace Λ V
      rw [cuspidal_iso_iff e]
      have h1 : ModuleCat.Hom.hom ((groupCohomology.functor ℂ Λ 1).mapIso e).hom (E.symm z) = z := E.apply_symm_apply z
      rw [h1]
      exact hz)

instance binaryPoly_fd (m : ℕ) : FiniteDimensional ℂ (GeneralEisenstein.Binary.HomogeneousPoly m) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ m)

variable {N : ℕ}

/-- `Sym^{m} ⊗ det^e` restricted to `Γ(N)`. -/
abbrev symRep (N : ℕ) (m : ℕ) (e : ℤ) : Rep ℂ (Gamma N) := Rep.res (Gamma N).subtype (modularBinaryRep m e)

instance symRep_fd (m : ℕ) (e : ℤ) : FiniteDimensional ℂ (symRep N m e) :=
  inferInstanceAs (FiniteDimensional ℂ (GeneralEisenstein.Binary.HomogeneousPoly m))

/-- **The apolar pairing of binary forms is a perfect `Γ(N)`-invariant pairing** (`SL₂` fixes it for every determinant twist). -/
theorem symRep_pairing (m : ℕ) (e e' : ℤ) :
    ∃ B : symRep N m e →ₗ[ℂ] symRep N m e' →ₗ[ℂ] ℂ,
      (∀ (γ : Gamma N) v w, B ((symRep N m e).ρ γ v) ((symRep N m e').ρ γ w) = B v w) ∧
        (∀ v, (∀ w, B v w = 0) → v = 0) ∧ (∀ w, (∀ v, B v w = 0) → w = 0) := by
  refine ⟨BinaryPairing.binaryPairing m, fun γ v w => ?_, fun v hv => BinaryPairing.binaryPairing_left_eq_zero m hv,
    fun w hw => BinaryPairing.binaryPairing_right_eq_zero m hw⟩
  exact BinaryPairing.binaryPairing_homogeneousAction_of_det_eq_one m e e'
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (Matrix.SpecialLinearGroup.toGL γ.1))
    (TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne.det_map_toGL γ.1) v w

/-- **The base pairing of the standard plane cusp of `Γ(N)` in binary coordinates**: through `H¹(N_P, E_n) ≅ Sym^{n+1} ⊗ det⁻¹`
(`gammaNCoordinateIso`) the apolar pairing of binary forms, i.e. the pairing whose parabolic cup product is the Petersson-type pairing
of the paper, perfectly pairs the mixed cuspidal group `𝒞_P(E_n)` with the cuspidal group of `Sym^{n+1}`. -/
theorem gammaNCuspidal_binary_pairing [NeZero N] (hN : 3 ≤ N) (n : ℕ) (e' : ℤ) :
    ∃ B : gammaNCuspidal N n →ₗ[ℂ] cuspidalSubspace (Gamma N) (symRep N (n + 1) e') →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) := by
  obtain ⟨e, hinv, hL, hR⟩ := symRep_pairing (N := N) (n + 1) (-1) e'
  obtain ⟨B', hl, hr⟩ := cuspidal_pairing_gammaN hN (symRep N (n + 1) (-1)) (symRep N (n + 1) e') e hinv hL hR
  obtain ⟨B, h1, h2, -⟩ := exists_transport (X := gammaNCuspidal N n) B' hl hr
    (cuspEquivOfIso (gammaNCoordinateIso N n)) (LinearEquiv.refl ℂ _)
  exact ⟨B, h1, h2⟩

end Binary

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
