module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalFacePairing

@[expose] public section


/-!
# The canonical (cup-form normalised) cuspidal pairing of `Γ(N)`

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

`cuspidal_pairing_gammaN` produces a perfect pairing of the cuspidal groups of Mathlib's `Γ(N)` by `Classical.choose`, with no normalisation.
Here the pairing is characterised by the explicit cup formula `cupForm` on classes of normalised twisted cusp functions
(`cuspidal_pairing_gammaN_cup`) and is UNIQUE with this property (`cuspidal_pairing_gammaN_unique`), so that it can be compared with
other normalisations of the face pairing up to an explicit scalar (the comparison constant is then a single number, not a choice).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open CongruenceSubgroup
open scoped Classical

variable {N : ℕ}

/-- The coupling of the transported modules induced by a perfect invariant pairing of `Γ(N)`-modules. -/
def couplingOf (hN : 3 ≤ N) {V V' : Rep ℂ (Gamma N)} (e : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hinv : ∀ (γ : Gamma N) v w, e (V.ρ γ v) (V'.ρ γ w) = e v w)
    (hL : ∀ v, (∀ w, e v w = 0) → v = 0) (hR : ∀ w, (∀ v, e v w = 0) → w = 0) :
    Coupling (transRep hN V).ρ (transRep hN V').ρ :=
  { e := e
    inv := fun γ v w => by
      have := hinv ((gammaEquiv hN).symm γ) v w
      exact this
    left := hL
    right := hR }

/-- **The cuspidal pairing of `Γ(N)` is the cup form.**  The perfect pairing of the literal cuspidal groups takes, on the classes of
normalised twisted cusp functions `Φ`, `Φ'` (of the transported modules), the explicit value `cupForm`. -/
theorem cuspidal_pairing_gammaN_cup (hN : 3 ≤ N) (V V' : Rep ℂ (Gamma N)) [FiniteDimensional ℂ V] [FiniteDimensional ℂ V']
    (e : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hinv : ∀ (γ : Gamma N) v w, e (V.ρ γ v) (V'.ρ γ w) = e v w)
    (hL : ∀ v, (∀ w, e v w = 0) → v = 0) (hR : ∀ w, (∀ v, e v w = 0) → w = 0) :
    ∃ B : cuspidalSubspace (Gamma N) V →ₗ[ℂ] cuspidalSubspace (Gamma N) V' →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
      ∀ (Φ : Tw (transRep hN V).ρ) (Φ' : Tw (transRep hN V').ρ), Φ.1 cusp1 = 0 →
        B ((cuspEquiv hN V).symm ⟨mTw (transRep hN V) Φ, mTw_mem_cuspidal _ Φ⟩)
          ((cuspEquiv hN V').symm ⟨mTw (transRep hN V') Φ', mTw_mem_cuspidal _ Φ'⟩) =
            cupForm hN (couplingOf hN e hinv hL hR) Φ.1 Φ'.1 := by
  obtain ⟨B', hl, hr, hB'⟩ := cuspidal_pairing_cup hN (transRep hN V) (transRep hN V') (couplingOf hN e hinv hL hR)
  obtain ⟨B, h1, h2, hB⟩ := exists_transport B' hl hr (cuspEquiv hN V) (cuspEquiv hN V')
  refine ⟨B, h1, h2, fun Φ Φ' h0 => ?_⟩
  rw [hB]
  simp only [LinearEquiv.apply_symm_apply]
  exact hB' Φ Φ' h0

/-- **Uniqueness**: a bilinear form on the cuspidal groups taking the cup-form values on the classes of normalised twisted cusp functions
is determined (every cuspidal class is such a class). -/
theorem cuspidal_pairing_gammaN_unique (hN : 3 ≤ N) (V V' : Rep ℂ (Gamma N))
    (B₁ B₂ : cuspidalSubspace (Gamma N) V →ₗ[ℂ] cuspidalSubspace (Gamma N) V' →ₗ[ℂ] ℂ)
    (h₁ : ∀ (Φ : Tw (transRep hN V).ρ) (Φ' : Tw (transRep hN V').ρ), Φ.1 cusp1 = 0 → Φ'.1 cusp1 = 0 →
      B₁ ((cuspEquiv hN V).symm ⟨mTw (transRep hN V) Φ, mTw_mem_cuspidal _ Φ⟩)
        ((cuspEquiv hN V').symm ⟨mTw (transRep hN V') Φ', mTw_mem_cuspidal _ Φ'⟩) =
      B₂ ((cuspEquiv hN V).symm ⟨mTw (transRep hN V) Φ, mTw_mem_cuspidal _ Φ⟩)
        ((cuspEquiv hN V').symm ⟨mTw (transRep hN V') Φ', mTw_mem_cuspidal _ Φ'⟩)) :
    B₁ = B₂ := by
  have key : ∀ x : cuspidalSubspace (Gamma N) V, ∃ Φ : Tw (transRep hN V).ρ, Φ.1 cusp1 = 0 ∧
      (cuspEquiv hN V).symm ⟨mTw (transRep hN V) Φ, mTw_mem_cuspidal _ Φ⟩ = x := by
    intro x
    obtain ⟨Φ, h0, hΦ⟩ := exists_Tn_of_cuspidal hN (transRep hN V) (x := (cuspEquiv hN V x).1) (cuspEquiv hN V x).2
    refine ⟨Φ, h0, ?_⟩
    apply (cuspEquiv hN V).injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext hΦ
  have key' : ∀ x : cuspidalSubspace (Gamma N) V', ∃ Φ : Tw (transRep hN V').ρ, Φ.1 cusp1 = 0 ∧
      (cuspEquiv hN V').symm ⟨mTw (transRep hN V') Φ, mTw_mem_cuspidal _ Φ⟩ = x := by
    intro x
    obtain ⟨Φ, h0, hΦ⟩ := exists_Tn_of_cuspidal hN (transRep hN V') (x := (cuspEquiv hN V' x).1) (cuspEquiv hN V' x).2
    refine ⟨Φ, h0, ?_⟩
    apply (cuspEquiv hN V').injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext hΦ
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨Φ, h0, rfl⟩ := key x
  obtain ⟨Φ', h0', rfl⟩ := key' y
  exact h₁ Φ Φ' h0 h0'

section Canonical

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull

/-- The Levi-invariant perfect pairing and its coupling, for the split extension `ℤ² → E → Γ(N)` and the literal contragredient. -/
def leviCoupling (hN : 3 ≤ N) {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
    (s : ext.Splitting) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (rep : Rep ℂ E) [FiniteDimensional ℂ rep] :
    Coupling (transRep hN (splitRadicalH1Representation s rep)).ρ
      (transRep hN (splitRadicalH1Representation s (dualRepG rep))).ρ :=
  have : FiniteDimensional ℂ (splitRadicalH1Representation s rep) := finiteDimensional_H1 (Rep.res ext.inl rep)
  have : FiniteDimensional ℂ (splitRadicalH1Representation s (dualRepG rep)) :=
    finiteDimensional_H1 (Rep.res ext.inl (dualRepG rep))
  couplingOf hN (radPairingOf (ext := ext) (perfectInv_dual rep))
    (fun γ x y => radPairingOf_levi (perfectInv_dual rep) s γ (hdet γ) x y)
    (fun x hx => radPairingOf_left (perfectInv_dual rep) x hx) (fun y hy => radPairingOf_right (perfectInv_dual rep) y hy)

/-- **The canonical face pairing** `𝒞(H¹(N_R, E)) × 𝒞(H¹(N_R, E^*)) → ℂ`: the cup-form pairing of the modular curve `X(N)` with coefficient
pairing the Levi-invariant Koszul pairing of the radical.  Unlike `cuspidal_literal_pairing` it has no free normalisation:
`facePairingCan_cup` fixes it on all classes of normalised twisted cusp functions. -/
def facePairingCan (hN : 3 ≤ N) {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
    (s : ext.Splitting) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (rep : Rep ℂ E) [FiniteDimensional ℂ rep] :
    cuspidalSubspace (Gamma N) (splitRadicalH1Representation s rep) →ₗ[ℂ]
      cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG rep)) →ₗ[ℂ] ℂ :=
  have : FiniteDimensional ℂ (splitRadicalH1Representation s rep) := finiteDimensional_H1 (Rep.res ext.inl rep)
  have : FiniteDimensional ℂ (splitRadicalH1Representation s (dualRepG rep)) :=
    finiteDimensional_H1 (Rep.res ext.inl (dualRepG rep))
  Classical.choose (cuspidal_pairing_gammaN_cup hN (splitRadicalH1Representation s rep)
    (splitRadicalH1Representation s (dualRepG rep)) (radPairingOf (ext := ext) (perfectInv_dual rep))
    (fun γ x y => radPairingOf_levi (perfectInv_dual rep) s γ (hdet γ) x y)
    (fun x hx => radPairingOf_left (perfectInv_dual rep) x hx) (fun y hy => radPairingOf_right (perfectInv_dual rep) y hy))

/-- The canonical face pairing is perfect on both sides. -/
theorem facePairingCan_perfect (hN : 3 ≤ N) {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
    (s : ext.Splitting) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (rep : Rep ℂ E) [FiniteDimensional ℂ rep] :
    (∀ x, (∀ y, facePairingCan hN s hdet rep x y = 0) → x = 0) ∧
      (∀ y, (∀ x, facePairingCan hN s hdet rep x y = 0) → y = 0) :=
  have : FiniteDimensional ℂ (splitRadicalH1Representation s rep) := finiteDimensional_H1 (Rep.res ext.inl rep)
  have : FiniteDimensional ℂ (splitRadicalH1Representation s (dualRepG rep)) :=
    finiteDimensional_H1 (Rep.res ext.inl (dualRepG rep))
  ⟨(Classical.choose_spec (cuspidal_pairing_gammaN_cup hN (splitRadicalH1Representation s rep)
    (splitRadicalH1Representation s (dualRepG rep)) (radPairingOf (ext := ext) (perfectInv_dual rep))
    (fun γ x y => radPairingOf_levi (perfectInv_dual rep) s γ (hdet γ) x y)
    (fun x hx => radPairingOf_left (perfectInv_dual rep) x hx) (fun y hy => radPairingOf_right (perfectInv_dual rep) y hy))).1,
   (Classical.choose_spec (cuspidal_pairing_gammaN_cup hN (splitRadicalH1Representation s rep)
    (splitRadicalH1Representation s (dualRepG rep)) (radPairingOf (ext := ext) (perfectInv_dual rep))
    (fun γ x y => radPairingOf_levi (perfectInv_dual rep) s γ (hdet γ) x y)
    (fun x hx => radPairingOf_left (perfectInv_dual rep) x hx) (fun y hy => radPairingOf_right (perfectInv_dual rep) y hy))).2.1⟩

/-- **The cup formula for the canonical face pairing**: on the classes of normalised twisted cusp functions it is `cupForm` for the
Levi-invariant Koszul coupling. -/
theorem facePairingCan_cup (hN : 3 ≤ N) {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
    (s : ext.Splitting) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (rep : Rep ℂ E) [FiniteDimensional ℂ rep]
    (Φ : Tw (transRep hN (splitRadicalH1Representation s rep)).ρ)
    (Φ' : Tw (transRep hN (splitRadicalH1Representation s (dualRepG rep))).ρ) (h0 : Φ.1 cusp1 = 0) :
    facePairingCan hN s hdet rep
        ((cuspEquiv hN (splitRadicalH1Representation s rep)).symm ⟨mTw _ Φ, mTw_mem_cuspidal _ Φ⟩)
        ((cuspEquiv hN (splitRadicalH1Representation s (dualRepG rep))).symm ⟨mTw _ Φ', mTw_mem_cuspidal _ Φ'⟩) =
      cupForm hN (leviCoupling hN s hdet rep) Φ.1 Φ'.1 :=
  have : FiniteDimensional ℂ (splitRadicalH1Representation s rep) := finiteDimensional_H1 (Rep.res ext.inl rep)
  have : FiniteDimensional ℂ (splitRadicalH1Representation s (dualRepG rep)) :=
    finiteDimensional_H1 (Rep.res ext.inl (dualRepG rep))
  (Classical.choose_spec (cuspidal_pairing_gammaN_cup hN (splitRadicalH1Representation s rep)
    (splitRadicalH1Representation s (dualRepG rep)) (radPairingOf (ext := ext) (perfectInv_dual rep))
    (fun γ x y => radPairingOf_levi (perfectInv_dual rep) s γ (hdet γ) x y)
    (fun x hx => radPairingOf_left (perfectInv_dual rep) x hx) (fun y hy => radPairingOf_right (perfectInv_dual rep) y hy))).2.2 Φ Φ' h0

end Canonical

section Faces

open scoped DirectSum MatrixGroups
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c (faceCuspidal faceRadH1 faceRep faceSplitting)

variable [NeZero N] (n : ℕ)

/-- **The canonical pairing of the line face `i`**, `𝒞_{Q'_i}(E_n) × 𝒞(H¹(N_{Q'_i}, E_n^*)) → ℂ` (`QDiLit`). -/
def pairQfaceCan (hN : 3 ≤ N) (i : LineFaces N) : lineFaceCuspidal N i.rep n →ₗ[ℂ] QDiLit N n i →ₗ[ℂ] ℂ :=
  facePairingCan hN (lineFaceSplitting N i.rep) (lineFaceRadicalInput_det N i.rep) (lineFaceRep N i.rep n)

theorem pairQfaceCan_perfect (hN : 3 ≤ N) (i : LineFaces N) :
    (∀ x, (∀ y, pairQfaceCan n hN i x y = 0) → x = 0) ∧ (∀ y, (∀ x, pairQfaceCan n hN i x y = 0) → y = 0) :=
  facePairingCan_perfect hN (lineFaceSplitting N i.rep) (lineFaceRadicalInput_det N i.rep) (lineFaceRep N i.rep n)

/-- **The canonical pairing of a plane face** `𝒞_{P'}(E_n) × 𝒞(H¹(N_{P'}, E_n^*)) → ℂ`. -/
def pairPfaceCan (hN : 3 ≤ N) (h : SL(3, ℤ)) :
    faceCuspidal N h n →ₗ[ℂ] cuspidalSubspace (Gamma N) (faceRadH1Lit N n h) →ₗ[ℂ] ℂ :=
  facePairingCan hN (faceSplitting N h) (planeFaceRadicalInput_det N h) (faceRep N h n)

theorem pairPfaceCan_perfect (hN : 3 ≤ N) (h : SL(3, ℤ)) :
    (∀ x, (∀ y, pairPfaceCan n hN h x y = 0) → x = 0) ∧ (∀ y, (∀ x, pairPfaceCan n hN h x y = 0) → y = 0) :=
  facePairingCan_perfect hN (faceSplitting N h) (planeFaceRadicalInput_det N h) (faceRep N h n)

/-- **`GammaNC5FaceObligations` with the canonical (cup-form normalised) line pairing**: the same as `ofRestLit` with the pairing
`pairQfaceCan`, which is characterised by `facePairingCan_cup` rather than chosen. -/
def GammaNC5FaceObligations.ofRestCan (hN : 3 ≤ N) {PD Hd : Type} [AddCommGroup PD] [Module ℂ PD] [AddCommGroup Hd] [Module ℂ Hd]
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
        ∀ c' : Hd, pairP ξP (rPd c') + sumPairing _ _ (pairQfaceCan n hN) ξQ (rQd c') = 0) :
    GammaNC5FaceObligations N n (QDiLit N n) PD Hd where
  T := T
  eisensteinP := eisensteinP
  Td := Td
  rPd := rPd
  rQd := rQd
  pairP := pairP
  pairQface := pairQfaceCan n hN
  dualEisenstein := dualEisenstein
  stokes := stokes
  perfectQface := fun i a h => (pairQfaceCan_perfect n hN i).1 a h

end Faces

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
