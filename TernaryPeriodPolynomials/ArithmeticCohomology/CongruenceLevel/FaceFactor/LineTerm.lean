module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CuspTotal
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Lift
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.LocalCusp
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.TwoCusps

@[expose] public section


/-!
# The flag term of a cusp: `λ_{F_c}[Θ_c] = -6 (r e(X_c, C'σ_c) - μ σ_c)`

Formalized by Claude Sonnet 5.5.

`flagLam_term`: for the flag `F_c = flagAt h (cuspPrim c)` over the line of `h`, the flag cocycle `Θ = cup12 w z' - γ` (`w` a primitive of the normal-form cocycle `z` on the flag group, `γ` a primitive of `z ∪ z'` vanishing on
radical triples) has `λ_{F_c}[Θ] = -6 (r e_C(Φ c + v, C'σ_c) - μ σ_c)`: `flagLam_eq_slant` (calibration), `chainEval_nuSh_flagTheta` (T2), `local_cusp_line`.
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD TernaryPeriodPolynomials.Argument.FlagH3
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open scoped Classical

section Term

variable (h : SL(3, ℤ)) (w : Prim2) (σ : Gamma 6) (hσ : ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ w.1 = w.1)
  (W : Rep ℂ ↥(gammaNQAt 6 h))
  (z : relativeTwoCocycles (lineFaceExt 6 h).inl W)
  (hmix : ∀ (r : RadicalLattice) (l : Gamma 6), z.val ((lineFaceExt 6 h).inl r, lineFaceSplitting 6 h l) = 0)
  (wB : ↥(MulAction.stabilizer Γ6 (flagAt h w)) → W)

/-- The primitive `wB` of the flag group, extended to a function on the line group. -/
def extendW : ↥(gammaNQAt 6 h) → W := fun g => wB (Function.invFun (flagIota h w) g)

theorem extendW_ι (b : ↥(MulAction.stabilizer Γ6 (flagAt h w))) : extendW h w W wB (flagIota h w b) = wB b := by
  unfold extendW
  rw [Function.leftInverse_invFun (flagIota_injective h w) b]

variable (hwB : ∀ b₁ b₂, W.ρ (flagIota h w b₁) (wB b₂) - wB (b₁ * b₂) + wB b₁ = z.val (flagIota h w b₁, flagIota h w b₂))

theorem flagIota_nlB (r : RadicalLattice) :
    flagIota h w ((flagLift h w σ hσ).nlB (Additive.ofMul r)) = (lineFaceExt 6 h).inl r :=
  ((flagLift h w σ hσ).hnl _).trans (pm_nl_ofMul _ r)

theorem flagIota_llB : flagIota h w (flagLift h w σ hσ).llB = lineFaceSplitting 6 h σ :=
  (flagLift h w σ hσ).hll.trans (pm_ll _ σ)

include hwB σ hσ in
theorem extendW_hR1 (r r' : RadicalLattice) :
    W.ρ ((lineFaceExt 6 h).inl r) (extendW h w W wB ((lineFaceExt 6 h).inl r')) -
      extendW h w W wB ((lineFaceExt 6 h).inl r * (lineFaceExt 6 h).inl r') + extendW h w W wB ((lineFaceExt 6 h).inl r) = 0 := by
  have e1 := flagIota_nlB h w σ hσ r
  have e2 := flagIota_nlB h w σ hσ r'
  have := hwB ((flagLift h w σ hσ).nlB (Additive.ofMul r)) ((flagLift h w σ hσ).nlB (Additive.ofMul r'))
  rw [e1, e2, z.property r r'] at this
  have k1 : extendW h w W wB ((lineFaceExt 6 h).inl r') = wB ((flagLift h w σ hσ).nlB (Additive.ofMul r')) := by
    rw [← e2, extendW_ι]
  have k2 : extendW h w W wB ((lineFaceExt 6 h).inl r) = wB ((flagLift h w σ hσ).nlB (Additive.ofMul r)) := by
    rw [← e1, extendW_ι]
  have k3 : extendW h w W wB ((lineFaceExt 6 h).inl r * (lineFaceExt 6 h).inl r') =
      wB ((flagLift h w σ hσ).nlB (Additive.ofMul r) * (flagLift h w σ hσ).nlB (Additive.ofMul r')) := by
    rw [← e1, ← e2, ← map_mul, extendW_ι]
  rw [k1, k2, k3]
  exact this

include hwB hmix hσ in
theorem extendW_hR2 (r : RadicalLattice) :
    W.ρ ((lineFaceExt 6 h).inl r) (extendW h w W wB (lineFaceSplitting 6 h σ)) -
      extendW h w W wB ((lineFaceExt 6 h).inl r * lineFaceSplitting 6 h σ) + extendW h w W wB ((lineFaceExt 6 h).inl r) = 0 := by
  have e1 := flagIota_nlB h w σ hσ r
  have e2 := flagIota_llB h w σ hσ
  have := hwB ((flagLift h w σ hσ).nlB (Additive.ofMul r)) (flagLift h w σ hσ).llB
  rw [e1, e2, hmix] at this
  have k1 : extendW h w W wB (lineFaceSplitting 6 h σ) = wB (flagLift h w σ hσ).llB := by
    rw [← e2, extendW_ι]
  have k2 : extendW h w W wB ((lineFaceExt 6 h).inl r) = wB ((flagLift h w σ hσ).nlB (Additive.ofMul r)) := by
    rw [← e1, extendW_ι]
  have k3 : extendW h w W wB ((lineFaceExt 6 h).inl r * lineFaceSplitting 6 h σ) =
      wB ((flagLift h w σ hσ).nlB (Additive.ofMul r) * (flagLift h w σ hσ).llB) := by
    rw [← e1, ← e2, ← map_mul, extendW_ι]
  rw [k1, k2, k3]
  exact this

include hwB hσ in
theorem extendW_hR3 (r : RadicalLattice) :
    W.ρ (lineFaceSplitting 6 h σ) (extendW h w W wB ((lineFaceExt 6 h).inl r)) -
      extendW h w W wB (lineFaceSplitting 6 h σ * (lineFaceExt 6 h).inl r) + extendW h w W wB (lineFaceSplitting 6 h σ) =
        z.val (lineFaceSplitting 6 h σ, (lineFaceExt 6 h).inl r) := by
  have e1 := flagIota_nlB h w σ hσ r
  have e2 := flagIota_llB h w σ hσ
  have := hwB (flagLift h w σ hσ).llB ((flagLift h w σ hσ).nlB (Additive.ofMul r))
  rw [e1, e2] at this
  have k1 : extendW h w W wB (lineFaceSplitting 6 h σ) = wB (flagLift h w σ hσ).llB := by
    rw [← e2, extendW_ι]
  have k2 : extendW h w W wB ((lineFaceExt 6 h).inl r) = wB ((flagLift h w σ hσ).nlB (Additive.ofMul r)) := by
    rw [← e1, extendW_ι]
  have k3 : extendW h w W wB (lineFaceSplitting 6 h σ * (lineFaceExt 6 h).inl r) =
      wB ((flagLift h w σ hσ).llB * (flagLift h w σ hσ).nlB (Additive.ofMul r)) := by
    rw [← e1, ← e2, ← map_mul, extendW_ι]
  rw [k1, k2, k3]
  exact this

end Term

section Main

/-- **The flag term at a cusp.**  `hwB`: `wB` is a primitive of `z` on the flag group; `Θ = cup12 wB z' - γ`. -/
theorem flagLam_term (hN : 3 ≤ 6) (h : SL(3, ℤ)) (w : Prim2) (σ : Gamma 6)
    (hσ : ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ w.1 = w.1) (hσpos : σ = posParSL w.1)
    (c : RationalLine2) (hσc : gammaEquiv hN σ = cuspSigma c)
    (hφσ : ∃ φ : Gamma 6 → ℚ, (∀ a b, φ (a * b) = φ a + φ b) ∧ φ σ ≠ 0)
    (W : Rep ℂ ↥(gammaNQAt 6 h)) [FiniteDimensional ℂ W] [Module ℚ W] [Module ℚ (dualRepG W)]
    (ρ' : Representation ℚ ↥(gammaNQAt 6 h) (dualRepG W)) (hρ' : ∀ g x, ρ' g x = (dualRepG W).ρ g x)
    (eQ : W →ₗ[ℚ] dualRepG W →ₗ[ℚ] ℚ) (r : ℂ →ₗ[ℚ] ℚ) (he : ∀ x y, eQ x y = r (Module.Dual.eval ℂ W x y))
    (z : relativeTwoCocycles (lineFaceExt 6 h).inl W) (z' : relativeTwoCocycles (lineFaceExt 6 h).inl (dualRepG W))
    (hmix : ∀ (r : RadicalLattice) (l : Gamma 6), z.val ((lineFaceExt 6 h).inl r, lineFaceSplitting 6 h l) = 0)
    (hmix' : ∀ (r : RadicalLattice) (l : Gamma 6), z'.val ((lineFaceExt 6 h).inl r, lineFaceSplitting 6 h l) = 0)
    (γ : ↥(gammaNQAt 6 h) → ↥(gammaNQAt 6 h) → ↥(gammaNQAt 6 h) → ℚ)
    (hγ : ∀ a b c : RadicalLattice, γ ((lineFaceExt 6 h).inl a) ((lineFaceExt 6 h).inl b) ((lineFaceExt 6 h).inl c) = 0)
    (wB : ↥(MulAction.stabilizer Γ6 (flagAt h w)) → W)
    (hwB : ∀ b₁ b₂, W.ρ (flagIota h w b₁) (wB b₂) - wB (b₁ * b₂) + wB b₁ = z.val (flagIota h w b₁, flagIota h w b₂))
    (hΘ : dThree ((flagLift h w σ hσ).flagTheta ρ' eQ wB (fun a b => z'.val (a, b)) γ) = 0)
    (Φ : Tw (transRep hN (splitRadicalH1Representation (lineFaceSplitting 6 h) W)).ρ)
    (v : splitRadicalH1Representation (lineFaceSplitting 6 h) W)
    (hCΦ : ∀ g : Gamma 6, (splitCocycleEdge (lineFaceSplitting 6 h) W z).1 g =
      fTw (transRep hN (splitRadicalH1Representation (lineFaceSplitting 6 h) W)) Φ.1 (gammaEquiv hN g) +
        (v - (splitRadicalH1Representation (lineFaceSplitting 6 h) W).ρ g v))
    (Φ' : Tw (transRep hN (splitRadicalH1Representation (lineFaceSplitting 6 h) (dualRepG W))).ρ)
    (v' : splitRadicalH1Representation (lineFaceSplitting 6 h) (dualRepG W))
    (hCΦ' : ∀ g : Gamma 6, (splitCocycleEdge (lineFaceSplitting 6 h) (dualRepG W) z').1 g =
      fTw (transRep hN (splitRadicalH1Representation (lineFaceSplitting 6 h) (dualRepG W))) Φ'.1 (gammaEquiv hN g) +
        (v' - (splitRadicalH1Representation (lineFaceSplitting 6 h) (dualRepG W)).ρ g v')) :
    flagLam (flagAt h w) (clsRes (MulAction.stabilizer Γ6 (flagAt h w)) _ hΘ) =
      -6 * (r ((leviCoupling hN (lineFaceSplitting 6 h) (lineFaceRadicalInput_det 6 h) W).e (Φ.1 c + v)
          ((splitCocycleEdge (lineFaceSplitting 6 h) (dualRepG W) z').1 σ)) -
        (pmE (lineFaceSplitting 6 h)).mu γ (Additive.ofMul latE1) (Additive.ofMul latE2) σ) := by
  have hdet := lineFaceRadicalInput_det 6 h
  have hl' := relativeTwoCocycle_radical_left (lineFaceSplitting 6 h) (dualRepG W) z' hmix'
  have hz'N : ∀ (a : Additive RadicalLattice) (g : ↥(gammaNQAt 6 h)),
      (fun a b => z'.val (a, b)) ((pmE (lineFaceSplitting 6 h)).nl a) g = 0 := fun a g => by
    show z'.val ((pmE (lineFaceSplitting 6 h)).nl a, g) = 0
    rw [pm_nl]; exact hl' _ _
  have hGe1 : (pmE (lineFaceSplitting 6 h)).Ge1 γ := fun a b c => by
    rw [pm_nl, pm_nl, pm_nl]; exact hγ _ _ _
  have hz := fun a b c => (flagLift h w σ hσ).flagTheta_nl ρ' eQ wB (fun a b => z'.val (a, b)) γ hz'N hGe1 a b c
  rw [flagLam_eq_slant h w σ hσ hσpos hdet hφσ _ hΘ hz,
    (flagLift h w σ hσ).chainEval_nuSh_flagTheta ρ' eQ wB (fun a b => z'.val (a, b)) γ hz'N]
  have hR1 := extendW_hR1 h w σ hσ W z wB hwB
  have hR2 := extendW_hR2 h w σ hσ W z hmix wB hwB
  have hR3 := extendW_hR3 h w σ hσ W z wB hwB
  have hloc := local_cusp_line (lineFaceSplitting 6 h) W hN hdet z z' hmix σ (extendW h w W wB) hR1 hR2 hR3 Φ v hCΦ Φ' v' hCΦ'
    c hσc
  have hA : eQ (wB ((flagLift h w σ hσ).nlB (Additive.ofMul latE1)))
        (ρ' ((pmE (lineFaceSplitting 6 h)).nl (Additive.ofMul latE1))
          ((fun a b => z'.val (a, b)) ((pmE (lineFaceSplitting 6 h)).ll σ)
            ((pmE (lineFaceSplitting 6 h)).nl ((pmE (lineFaceSplitting 6 h)).ψ σ⁻¹ (Additive.ofMul latE2))))) -
      eQ (wB ((flagLift h w σ hσ).nlB (Additive.ofMul latE2)))
        (ρ' ((pmE (lineFaceSplitting 6 h)).nl (Additive.ofMul latE2))
          ((fun a b => z'.val (a, b)) ((pmE (lineFaceSplitting 6 h)).ll σ)
            ((pmE (lineFaceSplitting 6 h)).nl ((pmE (lineFaceSplitting 6 h)).ψ σ⁻¹ (Additive.ofMul latE1))))) =
      r (altForm (Rep.res (lineFaceExt 6 h).inl (dualRepG W)).ρ (Module.Dual.eval ℂ W) (fun u => extendW h w W wB ((lineFaceExt 6 h).inl u))
        (fun r => splitEdgeCycle (lineFaceSplitting 6 h) (dualRepG W) σ z' r) latE1 latE2) := by
    have k1 : ∀ r : RadicalLattice, wB ((flagLift h w σ hσ).nlB (Additive.ofMul r)) = extendW h w W wB ((lineFaceExt 6 h).inl r) := by
      intro r
      rw [← flagIota_nlB h w σ hσ r, extendW_ι]
    rw [k1, k1]
    simp only [edge_val_ll_nl _ _ _ hmix', pm_nl_ofMul]
    unfold altForm
    simp only [he, map_sub]
    simp only [hρ']
    rfl
  rw [hA, hloc, map_neg]
  ring

end Main

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
