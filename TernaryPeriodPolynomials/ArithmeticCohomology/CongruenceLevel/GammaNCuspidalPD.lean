module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.C5Wiring
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspidalJ

@[expose] public section


/-!
# The base of the face pairing `ar:eq:facepair` for `Γ(N)`: Farey model, true compact-support map, cuspidal Poincaré-Lefschetz pairing

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair` and the paragraph: "On the base, the long exact sequence for a compactified modular curve identifies cuspidal
cohomology with the image of compactly supported cohomology. Poincaré-Lefschetz duality identifies the transpose of this
compact-support-to-ordinary map with the corresponding map for the dual local system. The induced pairing between the two images is
therefore nondegenerate."

**Distinct maps.**  `j_comb` (the auxiliary naive edge-identity map of `Exports/GammaNParabolicPD`, `gammaN_naive_parabolic_pairing`) is NOT the
topological map.  The topological compact-support map is `jTrue` below (`farey_jTrue`), defined through cusp potentials; its image is the
literal cuspidal subspace.

All statements are for `Γ(N)`, `N ≥ 3`, in the dual Farey tree model; `Γ(N)` is realised as `gammaNGL N ≤ GL₂(ℤ)` (free action on
triangles, finitely many orbits).  The transfer to Mathlib's `CongruenceSubgroup.Gamma N ≤ SL₂(ℤ)` and its `cuspidalSubspace` is
`farey_cuspidal_pairing_gamma` (and the face-level versions).

1. `farey_H1_iso`, `farey_H1_natural`: the Farey cochains `C¹/δC⁰` compute `groupCohomology.H1` through the path-sum cocycle, naturally in
   the coefficients.
2. `farey_jTrue`: the topological `j : H¹_c = ker d_c → H¹` has image exactly the cuspidal subspace (zero restriction to the stabilizer of every
   cusp) and kernel exactly the image of `H⁰` of the boundary (Farey differentials of cusp functions).
3. `farey_cuspidal_pairing`, `farey_cuspidal_pairing_cup`, `farey_cuspidal_pairing_skew`: the Poincaré-Lefschetz pairing of the cuspidal
   groups is perfect, is given by the explicit cup formula, and is skew under exchanging the two coefficient systems.
4. `farey_cuspidal_pairing_gamma`, `farey_lineFace_pairing`, `farey_planeFace_pairing`, `farey_planeCuspidal_binary_pairing`, and
   `GammaNC5FaceObligations.ofRest`: Mathlib's `Γ(N)`, the faces of the reduction of Proposition C.5, the binary coordinates of the plane
   face with the apolar pairing.

**Dual module.**  `QDiDual` is the cuspidal group of the *contragredient of the Levi module* `H¹(N_R, E_n)^∨`; the identification with the
paper's `H¹(N_R, E_n^*)` (literal contragredient coefficient system) through the Levi-invariant torus-fibre Koszul pairing at level `Γ(N)`
is `Exports/GammaNRadicalPD` (`farey_QDiLitEquiv`, `GammaNC5FaceObligations.ofRestLit`).

**Not proved here.**  The `stokes`, `eisensteinP`, `dualEisenstein`, `pairP` fields of `GammaNC5FaceObligations` are inputs to `ofRest`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.GammaNCuspidalPD

open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames

/-- **The dual Farey tree computes `H¹`**: `C¹/δC⁰ ≃ H¹(Γ, A)` through the path-sum cocycle, for any `Γ ≤ GL₂(ℤ)` acting freely on the
Farey triangles with finitely many orbits (`FareyData`). -/
def farey_H1_iso {Γ : Subgroup IntegralGL} (D : FareyData Γ) (A : Rep ℂ Γ) :
    (C1 A.ρ ⧸ LinearMap.range (delta A.ρ)) ≃ₗ[ℂ] groupCohomology.H1 A := cohIso A D

/-- The comparison is natural in the coefficients. -/
theorem farey_H1_natural {Γ : Subgroup IntegralGL} {A B : Rep ℂ Γ} (φ : A ⟶ B) (F : C1 A.ρ) :
    (groupCohomology.map (MonoidHom.id Γ) φ 1).hom (cohMap A F) = cohMap B (C1.map φ F) := cohMap_natural φ F

/-- **The topological compact-support map** `j : H¹_c(A) = ker d_c(A) → H¹(Γ(N), A)`: its image is the cuspidal subspace and its
kernel is the image of `H⁰` of the cusps. -/
theorem farey_jTrue {N : ℕ} (hN : 3 ≤ N) (A : Rep ℂ (gammaNGL N)) [FiniteDimensional ℂ A] :
    ∃ j : LinearMap.ker (dc A.ρ) →ₗ[ℂ] groupCohomology.H1 A,
      LinearMap.range j = cuspidalSub A ∧
        (∀ F : LinearMap.ker (dc A.ρ), j F = 0 ↔ F.1 ∈ LinearMap.range (bdryEq hN A.ρ)) := by
  obtain ⟨j, -, -, h1, h2⟩ := jTrue_exists hN A
  exact ⟨j, h1, h2⟩

/-- **The cuspidal Poincaré-Lefschetz pairing is perfect** (`Γ(N)`, `N ≥ 3`, finite dimensional modules with a perfect invariant pairing). -/
theorem farey_cuspidal_pairing {N : ℕ} (hN : 3 ≤ N) (A A' : Rep ℂ (gammaNGL N)) [FiniteDimensional ℂ A]
    [FiniteDimensional ℂ A'] (C : Coupling A.ρ A'.ρ) :
    ∃ B : cuspidalSub A →ₗ[ℂ] cuspidalSub A' →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) := by
  obtain ⟨B, h1, h2, -⟩ := cuspidal_pairing_exists hN A A' C
  exact ⟨B, h1, h2⟩

/-- **The explicit cup formula** for the pairing on classes of twisted cusp functions. -/
theorem farey_cuspidal_pairing_cup {N : ℕ} (hN : 3 ≤ N) (A A' : Rep ℂ (gammaNGL N)) [FiniteDimensional ℂ A]
    [FiniteDimensional ℂ A'] (C : Coupling A.ρ A'.ρ) :
    ∃ B : cuspidalSub A →ₗ[ℂ] cuspidalSub A' →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
      ∀ (Φ : Tw A.ρ) (Φ' : Tw A'.ρ), Φ.1 cusp1 = 0 →
        B ⟨mTw A Φ, mTw_mem_cuspidal A Φ⟩ ⟨mTw A' Φ', mTw_mem_cuspidal A' Φ'⟩ = cupForm hN C Φ.1 Φ'.1 :=
  cuspidal_pairing_cup hN A A' C

/-- **Skew-symmetry**: the pairings of `(A, A')` and of `(A', A)` are negatives of each other. -/
theorem farey_cuspidal_pairing_skew {N : ℕ} (hN : 3 ≤ N) (A A' : Rep ℂ (gammaNGL N)) [FiniteDimensional ℂ A]
    [FiniteDimensional ℂ A'] (C : Coupling A.ρ A'.ρ) :
    ∃ (B : cuspidalSub A →ₗ[ℂ] cuspidalSub A' →ₗ[ℂ] ℂ) (B' : cuspidalSub A' →ₗ[ℂ] cuspidalSub A →ₗ[ℂ] ℂ),
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
      (∀ y, (∀ x, B' y x = 0) → y = 0) ∧ (∀ x, (∀ y, B' y x = 0) → x = 0) ∧
      ∀ x y, B x y = - B' y x :=
  cuspidal_pairing_skew hN A A' C

/-- **The same for Mathlib's `Γ(N) ≤ SL₂(ℤ)` and its `cuspidalSubspace`**. -/
theorem farey_cuspidal_pairing_gamma {N : ℕ} (hN : 3 ≤ N) (V V' : Rep ℂ (CongruenceSubgroup.Gamma N))
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] (e : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hinv : ∀ (γ : CongruenceSubgroup.Gamma N) v w, e (V.ρ γ v) (V'.ρ γ w) = e v w)
    (hL : ∀ v, (∀ w, e v w = 0) → v = 0) (hR : ∀ w, (∀ v, e v w = 0) → w = 0) :
    ∃ B : TernaryPeriodPolynomials.Argument.SeedC3S4c.cuspidalSubspace (CongruenceSubgroup.Gamma N) V →ₗ[ℂ]
        TernaryPeriodPolynomials.Argument.SeedC3S4c.cuspidalSubspace (CongruenceSubgroup.Gamma N) V' →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) :=
  cuspidal_pairing_gammaN hN V V' e hinv hL hR

open scoped MatrixGroups in
/-- **The line faces**: `𝒞_{Q'}(E_n)` (`lineFaceCuspidal`, literal) is perfectly paired with the cuspidal group of the contragredient of its Levi
module `H¹(N_{Q'}, E_n)`. -/
theorem farey_lineFace_pairing {N : ℕ} [NeZero N] (hN : 3 ≤ N) (n : ℕ) (h : SL(3, ℤ)) :
    ∃ B : TernaryPeriodPolynomials.Argument.GammaNFaces.lineFaceCuspidal N h n →ₗ[ℂ]
        TernaryPeriodPolynomials.Argument.SeedC3S4c.cuspidalSubspace (CongruenceSubgroup.Gamma N)
          (dualRepG (TernaryPeriodPolynomials.Argument.GammaNFaces.lineFaceRadH1 N h n)) →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) :=
  lineFace_cuspidal_dual_pairing n h hN

open scoped MatrixGroups in
/-- **The plane faces**: the same for `𝒞_{P'}(E_n)` (`faceCuspidal`). -/
theorem farey_planeFace_pairing {N : ℕ} [NeZero N] (hN : 3 ≤ N) (n : ℕ) (h : SL(3, ℤ)) :
    ∃ B : TernaryPeriodPolynomials.Argument.SeedC3S4c.faceCuspidal N h n →ₗ[ℂ]
        TernaryPeriodPolynomials.Argument.SeedC3S4c.cuspidalSubspace (CongruenceSubgroup.Gamma N)
          (dualRepG (TernaryPeriodPolynomials.Argument.SeedC3S4c.faceRadH1 N h n)) →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) :=
  planeFace_cuspidal_dual_pairing n h hN

/-- **The standard plane cusp in binary coordinates**: `H¹(N_P, E_n) ≅ Sym^{n+1} ⊗ det⁻¹` and the apolar pairing of binary forms perfectly
pair `𝒞_P(E_n)` with the cuspidal group of `Sym^{n+1}` (any determinant twist, which is invisible on `Γ(N) ≤ SL₂`). -/
theorem farey_planeCuspidal_binary_pairing {N : ℕ} [NeZero N] (hN : 3 ≤ N) (n : ℕ) (e' : ℤ) :
    ∃ B : TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNCuspidal N n →ₗ[ℂ]
        TernaryPeriodPolynomials.Argument.SeedC3S4c.cuspidalSubspace (CongruenceSubgroup.Gamma N) (symRep N (n + 1) e') →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) :=
  gammaNCuspidal_binary_pairing hN n e'

end TernaryPeriodPolynomials.Argument.Statements.GammaNCuspidalPD
