module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.LocalCusp

@[expose] public section


/-!
# The local term at a cusp, planes (M3c(iii), plane analogue)

Formalized by Claude Sonnet 5.5.

`local_cusp_plane`: for a flag primitive `w'` of the normal-form cocycle `z'` of the dual module (radical cocycle `φ' = w' ∘ inl`) and the cusp data of `z`, the alternating form of
`(c̃σ z, σ·φ')` on `(e₁, e₂)` is `+⟨Φ c + v, C'σ⟩`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open CongruenceSubgroup
open scoped Classical MatrixGroups

variable {N : ℕ}

section Plane

variable {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)} (s : ext.Splitting) (W : Rep ℂ E)
  [FiniteDimensional ℂ W]

/-- **Local cusp, planes**: with `C σ = (1-σ)X` and `w'` a flag primitive of `z'`, the alternating form of `(c̃σ z, σ·φ')`
is `⟨X, C'σ⟩`. -/
theorem local_cusp_plane_gen (hN : 3 ≤ N) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1)
    (z : relativeTwoCocycles ext.inl W) (z' : relativeTwoCocycles ext.inl (dualRepG W))
    (hmix' : ∀ (r : RadicalLattice) (l : Gamma N), z'.val (ext.inl r, s l) = 0) (σ : Gamma N) (w' : E → dualRepG W)
    (hR1 : ∀ r r' : RadicalLattice,
      (dualRepG W).ρ (ext.inl r) (w' (ext.inl r')) - w' (ext.inl r * ext.inl r') + w' (ext.inl r) = 0)
    (hR2 : ∀ r : RadicalLattice,
      (dualRepG W).ρ (ext.inl r) (w' (s σ)) - w' (ext.inl r * s σ) + w' (ext.inl r) = 0)
    (hR3 : ∀ r : RadicalLattice,
      (dualRepG W).ρ (s σ) (w' (ext.inl r)) - w' (s σ * ext.inl r) + w' (s σ) = z'.val (s σ, ext.inl r))
    (X : groupCohomology.H1 (Rep.res ext.inl W))
    (hX : (splitCocycleEdge s W z).1 σ = X - splitRadicalH1Action s W σ X) :
    altForm (Rep.res ext.inl (dualRepG W)).ρ (Module.Dual.eval ℂ W) (fun r => splitEdgeCycle s W σ z r)
        (splitRadicalCocycleAction s (dualRepG W) σ (flagRadCocycle (dualRepG W) w' hR1)).1 latE1 latE2 =
      (leviCoupling hN s hdet W).e X ((splitCocycleEdge s (dualRepG W) z').1 σ) := by
  have hP := flag_class_relation s (dualRepG W) z' hmix' σ w' hR1 hR2 hR3
  have e1 : altForm (Rep.res ext.inl (dualRepG W)).ρ (Module.Dual.eval ℂ W) (fun r => splitEdgeCycle s W σ z r)
        (splitRadicalCocycleAction s (dualRepG W) σ (flagRadCocycle (dualRepG W) w' hR1)).1 latE1 latE2 =
      radPairingOf (ext := ext) (perfectInv_dual W) (groupCohomology.H1π _ (splitEdgeCycle s W σ z))
        (splitRadicalH1Action s (dualRepG W) σ (groupCohomology.H1π _ (flagRadCocycle (dualRepG W) w' hR1))) := by
    rw [splitRadicalH1Action_apply, radPairingOf_spec]
    rfl
  have e2 : groupCohomology.H1π _ (splitEdgeCycle s W σ z) = X - splitRadicalH1Action s W σ X := by
    rw [← splitCocycleEdge_val]
    exact hX
  have h1 := radPairingOf_levi (ext := ext) (perfectInv_dual W) s σ (hdet σ) X
    (groupCohomology.H1π _ (flagRadCocycle (dualRepG W) w' hR1))
  have e3 : (splitCocycleEdge s (dualRepG W) z').1 σ = groupCohomology.H1π _ (splitEdgeCycle s (dualRepG W) σ z') :=
    splitCocycleEdge_val s (dualRepG W) z' σ
  rw [e1, e2, e3, ← hP]
  show _ = radPairingOf (ext := ext) (perfectInv_dual W) X _
  simp only [map_sub, LinearMap.sub_apply]
  linear_combination (-1 : ℂ) * h1

/-- **Local cusp, planes**, with the cusp data `C = fTw Φ + (v - ρ v)` of `edge_pairing_cusp_sum`. -/
theorem local_cusp_plane (hN : 3 ≤ N) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1)
    (z : relativeTwoCocycles ext.inl W) (z' : relativeTwoCocycles ext.inl (dualRepG W))
    (hmix' : ∀ (r : RadicalLattice) (l : Gamma N), z'.val (ext.inl r, s l) = 0) (σ : Gamma N) (w' : E → dualRepG W)
    (hR1 : ∀ r r' : RadicalLattice,
      (dualRepG W).ρ (ext.inl r) (w' (ext.inl r')) - w' (ext.inl r * ext.inl r') + w' (ext.inl r) = 0)
    (hR2 : ∀ r : RadicalLattice,
      (dualRepG W).ρ (ext.inl r) (w' (s σ)) - w' (ext.inl r * s σ) + w' (ext.inl r) = 0)
    (hR3 : ∀ r : RadicalLattice,
      (dualRepG W).ρ (s σ) (w' (ext.inl r)) - w' (s σ * ext.inl r) + w' (s σ) = z'.val (s σ, ext.inl r))
    (Φ : Tw (transRep hN (splitRadicalH1Representation s W)).ρ) (v : splitRadicalH1Representation s W)
    (hCΦ : ∀ g : Gamma N, (splitCocycleEdge s W z).1 g =
      fTw (transRep hN (splitRadicalH1Representation s W)) Φ.1 (gammaEquiv hN g) +
        (v - (splitRadicalH1Representation s W).ρ g v))
    (c : RationalLine2) (hσ : gammaEquiv hN σ = cuspSigma c) :
    altForm (Rep.res ext.inl (dualRepG W)).ρ (Module.Dual.eval ℂ W) (fun r => splitEdgeCycle s W σ z r)
        (splitRadicalCocycleAction s (dualRepG W) σ (flagRadCocycle (dualRepG W) w' hR1)).1 latE1 latE2 =
      (leviCoupling hN s hdet W).e (Φ.1 c + v) ((splitCocycleEdge s (dualRepG W) z').1 σ) :=
  local_cusp_plane_gen s W hN hdet z z' hmix' σ w' hR1 hR2 hR3 (Φ.1 c + v) (edge_val_cusp hN _ _ Φ v hCΦ c σ hσ)

end Plane

section Cup21

variable {E L : Type} [Group E] [Group L] {ext : GroupExtension RadicalLattice E L} (s : ext.Splitting)
  {V W' : Rep ℂ E} [Module ℚ V] [Module ℚ W'] (ρ' : Representation ℚ E W')
  (hρ' : ∀ g x, ρ' g x = W'.ρ g x) (e : V →ₗ[ℚ] W' →ₗ[ℚ] ℚ)

/-- **T2, `z ∪ w`** (extension language): `⟨cup21 z w, Sh(v₁ v₂; σ)⟩ = e(c̃σ v₁, (v₁ · s σ) · w(σ · v₂))`. -/
theorem T2_cup21 (z : relativeTwoCocycles ext.inl V)
    (hmix : ∀ (r : RadicalLattice) (l : L), z.val (ext.inl r, s l) = 0) (w : E → W') (v₁ v₂ : RadicalLattice) (σ : L) :
    (pmE s).sh1 (cup21 ρ' e (fun a b => z.val (a, b)) w) (Additive.ofMul v₁) (Additive.ofMul v₂) σ =
      e (splitEdgeCycle s V σ z v₁) (ρ' (ext.inl v₁ * s σ) (w (ext.inl (splitRadicalInput s σ v₂)))) := by
  have h1 : z.val (s σ, ext.inl (splitRadicalInput s σ v₁)) = splitEdgeCycle s V σ z v₁ := by
    rw [splitEdgeCycle_apply, hmix, sub_zero]
  unfold PairModel.sh1 cup21
  simp only [pm_ll, pm_psi_inv, pm_nl_ofMul]
  rw [h1, hmix, z.2 v₁ v₂, ← splitRadicalInput_commute]
  simp

include hρ' in
/-- `⟨cup21 z w, Sh(ν; σ)⟩ = r (altForm (c̃σ z) (σ·φ') e₁ e₂)` for `e = r ∘ eC`, `φ' = w ∘ inl`. -/
theorem mu_cup21_alt (eC : V →ₗ[ℂ] W' →ₗ[ℂ] ℂ) (r : ℂ →ₗ[ℚ] ℚ) (he : ∀ x y, e x y = r (eC x y))
    (z : relativeTwoCocycles ext.inl V) (hmix : ∀ (r : RadicalLattice) (l : L), z.val (ext.inl r, s l) = 0)
    (φ' : groupCohomology.cocycles₁ (Rep.res ext.inl W')) (w : E → W') (hw : ∀ u, φ' u = w (ext.inl u)) (σ : L) :
    (pmE s).mu (cup21 ρ' e (fun a b => z.val (a, b)) w) (Additive.ofMul latE1) (Additive.ofMul latE2) σ =
      r (altForm (Rep.res ext.inl W').ρ eC (fun u => splitEdgeCycle s V σ z u)
        (splitRadicalCocycleAction s W' σ φ').1 latE1 latE2) := by
  have hφ : ∀ u, (splitRadicalCocycleAction s W' σ φ').1 u = W'.ρ (s σ) (w (ext.inl (splitRadicalInput s σ u))) := by
    intro u
    rw [← hw]
    rfl
  unfold PairModel.mu
  rw [T2_cup21 s ρ' e z hmix, T2_cup21 s ρ' e z hmix]
  unfold altForm
  simp only [he, map_sub, hφ, hρ', map_mul, Module.End.mul_apply]
  rfl

end Cup21

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
