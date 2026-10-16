module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalLineCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.FaceCanonical

@[expose] public section


/-!
# The face pairing `ar:eq:facepair` for `Γ(N)` with the literal contragredient `H¹(N_R, E_n^*)`

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair` and: "The two-generator Koszul complex for the radical pairs degree one with degree one into its top
orientation line.  This is Poincaré duality on its compact torus fiber with dual local systems. ... Combining the two pairings proves
`ar:eq:facepair`.  The two internal orientation characters multiply to the face orientation. All determinant and reflection actions are
retained before taking finite-group invariants."

This completes the half of `Exports/GammaNCuspidalPD` (whose base pairing is the cuspidal Poincaré-Lefschetz pairing of the modular
curve `X(N)`): the **fibre** pairing of the radical `N_R ≅ ℤ²` is built and shown Levi-invariant, so that the dual module of the face
`R ∈ {P, Q}` is the cuspidal group of the Levi module `H¹(N_R, E_n^*)` of the *literal contragredient* coefficient system.

1. `radical_koszul_pairing`: for `ℤ²` acting on finite-dimensional `A, A'` with a perfect invariant pairing, the Koszul/cup pairing
   `⟨c, c'⟩ = e(c(s₁), s₁ c'(s₂)) - e(c(s₂), s₂ c'(s₁))` descends to a PERFECT pairing of `groupCohomology.H1`; it is the torus-fibre
   Koszul pairing (`PhiC_eq_Phi` is definitional).  `radical_koszul_levi_invariant`: it is invariant under the Levi action
   `splitRadicalH1Representation` of every Levi element acting on the radical with determinant one.
2. The Levi of the line group and of the plane group of every conjugate cusp acts with determinant one (`lineFaceRadicalInput_det`,
   `planeFaceRadicalInput_det`), whence `lineFace_literal_pairing`, `planeFace_literal_pairing`: the cuspidal groups
   `𝒞_{R'}(E_n)` and `𝒞(H¹(N_{R'}, E_n^*))` are perfectly paired.
3. `QDiLitEquiv` (and `lineFaceLitIso`, `planeFaceLitIso`): `H¹(N_R, E^*) ≅ H¹(N_R, E)^∨` as `Γ(N)`-modules, so the dual module of the
   earlier wiring (`QDiDual`, the contragredient of the Levi module) IS the paper's dual module.
4. Binary coordinates at level `Γ(N)`: plane (`planeFace_binary_iso`, all conjugates; Lemma C.3) `Sym^{n+1} ⊗ det⁻¹`, line
   (`line_coordinate_iso`, `lineFace_binary_iso`, all conjugates) `Sym^{n+1}` (twist `0`); the literal contragredient is `Sym^{n+1}`
   (`planeFaceLit_binary_iso`, `lineFaceLit_binary_iso`); the apolar pairing perfectly pairs the line cuspidal groups
   (`lineFace_binary_pairing`).  On `Γ(N) ≤ SL₂(ℤ)` the determinant twist is invisible; it is retained for `GL₂(ℤ)` in the library's
   `lowerRadicalH1Coordinate_equivariant` (twist `0`) and `upperRadicalH1Coordinate_equivariant` (twist `-1`).

5. The canonical (cup-form normalised) face pairing: `facePairingCan_cup` (value `cupForm` for the Levi-invariant Koszul coupling on the classes of
   normalised twisted cusp functions), `cuspidal_pairing_gammaN_unique` (uniqueness), `pairQfaceCan`/`pairPfaceCan` (all faces, perfect) and
   `GammaNC5FaceObligations.ofRestCan`.  This removes the free normalisation of `pairQfaceLit` (a `Classical.choose`), so a comparison with a
   geometric normalisation is a statement about ONE explicit scalar.

**Not proved here.**  The comparison of the geometric cone pairings `lineFacePairM`/`planeFacePairM` with `pairQfaceCan`/`pairPfaceCan`, the comparison of the Farey cup formula `cupForm` with the three-puncture formula `pdRaw` of
`Glue/FacePDBinaryPLRel` (binary Levi `Γ₁'(3)`, `GL₂(ℤ)`), the `stokes`, `eisensteinP`, `dualEisenstein`, `pairP` fields of
`GammaNC5FaceObligations`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.GammaNRadicalPD

open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- **The torus-fibre Koszul pairing of the radical lattice is a perfect pairing of `H¹`.** -/
theorem radical_koszul_pairing {A A' : Rep ℂ RadicalLattice} {e : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ}
    (he : ∀ g a b, e (A.ρ g a) (A'.ρ g b) = e a b) (hl : ∀ a, (∀ b, e a b = 0) → a = 0)
    (hr : ∀ b, (∀ a, e a b = 0) → b = 0) [FiniteDimensional ℂ A] [FiniteDimensional ℂ A'] :
    ∃ B : groupCohomology.H1 A →ₗ[ℂ] groupCohomology.H1 A' →ₗ[ℂ] ℂ,
      (∀ c c', B (groupCohomology.H1π A c) (groupCohomology.H1π A' c') = PhiC A A' e c c') ∧
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) :=
  exists_radPairing he hl hr

/-- **Levi invariance of the radical pairing**: invariant under `splitRadicalH1Representation` of every Levi element whose action on the
radical lattice has determinant one. -/
theorem radical_koszul_levi_invariant {E L : Type} [Group E] [Group L] {ext : GroupExtension RadicalLattice E L}
    {rep rep' : Rep ℂ E} {e : rep →ₗ[ℂ] rep' →ₗ[ℂ] ℂ} (hp : PerfectInv e) [FiniteDimensional ℂ rep]
    [FiniteDimensional ℂ rep'] (s : ext.Splitting) (m : L) (hdet : radDet (splitRadicalInput s m) = 1)
    (x : groupCohomology.H1 (Rep.res ext.inl rep)) (y : groupCohomology.H1 (Rep.res ext.inl rep')) :
    radPairingOf (ext := ext) hp (splitRadicalH1Action s rep m x) (splitRadicalH1Action s rep' m y) =
      radPairingOf (ext := ext) hp x y :=
  radPairingOf_levi hp s m hdet x y

open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace faceCuspidal faceRadH1)
open CongruenceSubgroup

/-- **The line faces, literal contragredient**: `𝒞_{Q'}(E_n)` is perfectly paired with `𝒞(H¹(N_{Q'}, E_n^*))` (`N ≥ 3`). -/
theorem farey_lineFace_literal_pairing {N : ℕ} [NeZero N] (hN : 3 ≤ N) (n : ℕ) (h : SL(3, ℤ)) :
    ∃ B : lineFaceCuspidal N h n →ₗ[ℂ] cuspidalSubspace (Gamma N) (lineFaceRadH1Lit N n h) →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) :=
  lineFace_literal_pairing n h hN

/-- **The plane faces, literal contragredient**: `𝒞_{P'}(E_n)` is perfectly paired with `𝒞(H¹(N_{P'}, E_n^*))` (`N ≥ 3`). -/
theorem farey_planeFace_literal_pairing {N : ℕ} [NeZero N] (hN : 3 ≤ N) (n : ℕ) (h : SL(3, ℤ)) :
    ∃ B : faceCuspidal N h n →ₗ[ℂ] cuspidalSubspace (Gamma N) (faceRadH1Lit N n h) →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) :=
  planeFace_literal_pairing n h hN

/-- **`H¹(N_{Q'}, E_n^*) ≅ H¹(N_{Q'}, E_n)^∨`** as `Γ(N)`-modules (line faces). -/
def farey_lineFace_literal_iso {N : ℕ} [NeZero N] (n : ℕ) (h : SL(3, ℤ)) :
    lineFaceRadH1Lit N n h ≅ dualRepG (lineFaceRadH1 N h n) := lineFaceLitIso N n h

/-- **`H¹(N_{P'}, E_n^*) ≅ H¹(N_{P'}, E_n)^∨`** as `Γ(N)`-modules (plane faces). -/
def farey_planeFace_literal_iso {N : ℕ} [NeZero N] (n : ℕ) (h : SL(3, ℤ)) :
    faceRadH1Lit N n h ≅ dualRepG (faceRadH1 N h n) := planeFaceLitIso N n h

/-- **The dual module of the earlier wiring is the paper's dual module**: for every line face the cuspidal group of the Levi module of the
literal contragredient is linearly isomorphic to the cuspidal group of the contragredient of the Levi module. -/
def farey_QDiLitEquiv {N : ℕ} [NeZero N] (n : ℕ) (i : TernaryPeriodPolynomials.Argument.GammaNFacesFull.LineFaces N) :
    QDiLit N n i ≃ₗ[ℂ] QDiDual N n i := QDiLitEquiv N n i

/-- **The standard line cusp in binary coordinates**: `H¹(N_Q, E_n) ≅ Sym^{n+1}` (twist `0`) as `Γ(N)`-modules, every `n`. -/
def farey_line_coordinate_iso {N : ℕ} [NeZero N] (n : ℕ) : lineRadH1 N n ≅ symRep N (n + 1) 0 := lineCoordinateIso N n

/-- **Every conjugate line cusp in binary coordinates.** -/
def farey_lineFace_binary_iso {N : ℕ} [NeZero N] (n : ℕ) (h : SL(3, ℤ)) : lineFaceRadH1 N h n ≅ symRep N (n + 1) 0 :=
  lineFaceBinaryIso N n h

/-- **Every conjugate plane cusp in binary coordinates**: `H¹(N_{P'}, E_n) ≅ Sym^{n+1} ⊗ det⁻¹`. -/
def farey_planeFace_binary_iso {N : ℕ} [NeZero N] (n : ℕ) (h : SL(3, ℤ)) : faceRadH1 N h n ≅ symRep N (n + 1) (-1) :=
  faceBinaryIso N n h

/-- The literal contragredient of a conjugate line cusp in binary coordinates: `Sym^{n+1}`. -/
def farey_lineFaceLit_binary_iso {N : ℕ} [NeZero N] (n : ℕ) (h : SL(3, ℤ)) : lineFaceRadH1Lit N n h ≅ symRep N (n + 1) 0 :=
  lineFaceLitBinaryIso N n h

/-- The literal contragredient of a conjugate plane cusp in binary coordinates: `Sym^{n+1}`. -/
def farey_planeFaceLit_binary_iso {N : ℕ} [NeZero N] (n : ℕ) (h : SL(3, ℤ)) : faceRadH1Lit N n h ≅ symRep N (n + 1) 0 :=
  planeFaceLitBinaryIso N n h

/-- **The line cusps in binary coordinates**: the apolar pairing perfectly pairs `𝒞_{Q'}(E_n)` with the cuspidal group of `Sym^{n+1}`. -/
theorem farey_lineFace_binary_pairing {N : ℕ} [NeZero N] (hN : 3 ≤ N) (n : ℕ) (h : SL(3, ℤ)) (e' : ℤ) :
    ∃ B : lineFaceCuspidal N h n →ₗ[ℂ] cuspidalSubspace (Gamma N) (symRep N (n + 1) e') →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) :=
  lineFaceCuspidal_binary_pairing n h hN e'

/-- **The cuspidal pairing of `Γ(N)` is determined by the cup form** (every cuspidal class is the class of a normalised twisted cusp function). -/
theorem farey_cuspidal_pairing_unique {N : ℕ} (hN : 3 ≤ N) (V V' : Rep ℂ (Gamma N))
    (B₁ B₂ : cuspidalSubspace (Gamma N) V →ₗ[ℂ] cuspidalSubspace (Gamma N) V' →ₗ[ℂ] ℂ)
    (h₁ : ∀ (Φ : Tw (transRep hN V).ρ)
      (Φ' : Tw (transRep hN V').ρ),
      Φ.1 TernaryPeriodPolynomials.Argument.FareyTree.cusp1 = 0 → Φ'.1 TernaryPeriodPolynomials.Argument.FareyTree.cusp1 = 0 →
      B₁ ((cuspEquiv hN V).symm ⟨mTw (transRep hN V) Φ, mTw_mem_cuspidal _ Φ⟩)
        ((cuspEquiv hN V').symm ⟨mTw (transRep hN V') Φ', mTw_mem_cuspidal _ Φ'⟩) =
      B₂ ((cuspEquiv hN V).symm ⟨mTw (transRep hN V) Φ, mTw_mem_cuspidal _ Φ⟩)
        ((cuspEquiv hN V').symm ⟨mTw (transRep hN V') Φ', mTw_mem_cuspidal _ Φ'⟩)) :
    B₁ = B₂ := cuspidal_pairing_gammaN_unique hN V V' B₁ B₂ h₁

end TernaryPeriodPolynomials.Argument.Statements.GammaNRadicalPD
