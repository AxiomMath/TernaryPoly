module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.PlaneFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Plane.Flag
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.FrameLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.CuspConjNat
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineCanTransport

@[expose] public section


/-!
# Frame invariance of the canonical plane pairing (generic coefficients)

Formalized by Claude Sonnet 5.5.

`canAtP_transport`: for `h' = q h γ` (`q ∈ planeBorel`, `γ ∈ SL₃(ℤ)`), any coefficient modules `W₁` of the plane group of `h`, `W₂` of that of `h'` related by `T : W₁ ≃ W₂` with `T (W₁(γ p γ⁻¹) v) = W₂(p) (T v)`,
and any mixed classes `x`, `y` (coefficients `W₁`, `W₁^*`), the transports of `x`, `y` are mixed and have the same canonical pairing: `canAt h' (Θx) (Θ'y) = canAt h x y`.  The orientation sign `det(φ_q) · det(A_G) = d² = 1`
(`planeFrame_sign`) is the product of the Koszul sign and the cup-form sign.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.SeedC3
open CongruenceSubgroup TernaryPoly.RankTwoAugmentedFrames


variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h q γ : SL(3, ℤ)) (hq : q ∈ planeBorel)
  (W₁ : Rep ℂ (gammaNPAt N h)) (W₂ : Rep ℂ (gammaNPAt N (q * h * γ))) (T : W₁ ≃ₗ[ℂ] W₂)
  (hT : ∀ (g : gammaNPAt N (q * h * γ)) (v : W₁),
    T (W₁.ρ ((planeFrameEquiv N hN h q γ hq).θ g) v) = W₂.ρ g (T v))

theorem h2X_eq_h2Map_plane :
    h2X (planeFrameEquiv N hN h q γ hq) W₁ W₂ T hT =
      SeedC3S4c.EdgeNat.h2Map (planeFrameEquiv N hN h q γ hq).θ.toMonoidHom W₁ W₂ T.toLinearMap hT := rfl


theorem planeMixed_transport (x : groupCohomology.H2 W₁) (hx : x ∈ planeMixedAt N h W₁) :
    h2X (planeFrameEquiv N hN h q γ hq) W₁ W₂ T hT x ∈ planeMixedAt N (q * h * γ) W₂ := by
  refine (Submodule.mem_iInf _).2 fun F' => LinearMap.mem_ker.2 ?_
  set F : GL (Fin 2) ℚ := castGL (topLeft q⁻¹) (topLeft q) (topLeft_inv_mul q hq).2 (topLeft_inv_mul q hq).1 * F' with hF
  have hmem : ∀ k : faceFlagStab N (q * h * γ) F',
      (planeFrameEquiv N hN h q γ hq).θ k.1 ∈ faceFlagStab N h F := fun k =>
    (faceFlagStab_iff_chain N N h (q * h * γ) q γ hq rfl k.1.1 k.1.2 (γ * k.1.1 * γ⁻¹)
      ((planeFrameEquiv N hN h q γ hq).θ k.1).2 rfl F').mp k.2
  let κ : faceFlagStab N (q * h * γ) F' →* faceFlagStab N h F :=
    ((planeFrameEquiv N hN h q γ hq).θ.toMonoidHom.comp (faceFlagStab N (q * h * γ) F').subtype).codRestrict _ hmem
  exact res_h2X_eq_zero _ W₁ W₂ T hT (faceFlagStab N h F).subtype (faceFlagStab N (q * h * γ) F').subtype κ
    (fun _ => rfl) x (planeMixedAt_apply hx F)


include hT in
theorem planeFrame_hTdual : ∀ (g : gammaNPAt N (q * h * γ)) (φ : Module.Dual ℂ W₁),
    dualEquiv W₁ W₂ T ((dualRepG W₁).ρ ((planeFrameEquiv N hN h q γ hq).θ g) φ) = (dualRepG W₂).ρ g (dualEquiv W₁ W₂ T φ) :=
  FrameInvariance.hTdual (planeFrameEquiv N hN h q γ hq) W₁ W₂ T hT

variable [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂]

omit [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂] in
theorem planeMixedEdgeAt_transport (x : groupCohomology.H2 W₁) (hx : x ∈ planeMixedAt N h W₁) :
    planeMixedEdgeAt N (q * h * γ) W₂ ⟨h2X (planeFrameEquiv N hN h q γ hq) W₁ W₂ T hT x,
      planeMixed_transport N hN h q γ hq W₁ W₂ T hT x hx⟩ =
      cuspXi hN (alphaP hN hq) (AGP hq) (alphaP_glConj hN hq) _ _
        (leviMap (planeFrameEquiv N hN h q γ hq) (faceSplitting N h) (faceSplitting N (q * h * γ)) W₁ W₂ T hT)
        (leviMap_equiv (planeFrameEquiv N hN h q γ hq) (faceSplitting N h) (faceSplitting N (q * h * γ)) W₁ W₂ T hT)
        (planeMixedEdgeAt N h W₁ ⟨x, hx⟩) := by
  apply Subtype.ext
  exact edge_kerMapX (planeFrameEquiv N hN h q γ hq) W₁ W₂ T hT (faceSplitting N h)
    (faceSplitting N (q * h * γ)) ⟨x, res_radical_of_planeMixedAt ⟨x, hx⟩⟩


/-- **Frame invariance of the canonical line pairing, for arbitrary coefficient modules.**  The transports of mixed classes `x`, `y` (coefficients `W₁`, `W₁^*`) along the frame change `h ↦ q h γ` are mixed and have
the same canonical pairing; the orientation sign `det(φ_q) · det(A_G) = d² = 1` does not appear. -/
theorem canAtP_transport (hconj : CuspConjNat N hN) (x : groupCohomology.H2 W₁) (hx : x ∈ planeMixedAt N h W₁)
    (y : groupCohomology.H2 (dualRepG W₁)) (hy : y ∈ planeMixedAt N h (dualRepG W₁)) :
    canAtP N (q * h * γ) hN W₂
        ⟨h2X (planeFrameEquiv N hN h q γ hq) W₁ W₂ T hT x, planeMixed_transport N hN h q γ hq W₁ W₂ T hT x hx⟩
        ⟨h2X (planeFrameEquiv N hN h q γ hq) (dualRepG W₁) (dualRepG W₂) (dualEquiv W₁ W₂ T)
          (planeFrame_hTdual N hN h q γ hq W₁ W₂ T hT) y,
          planeMixed_transport N hN h q γ hq (dualRepG W₁) (dualRepG W₂) (dualEquiv W₁ W₂ T)
            (planeFrame_hTdual N hN h q γ hq W₁ W₂ T hT) y hy⟩ =
      canAtP N h hN W₁ ⟨x, hx⟩ ⟨y, hy⟩ := by
  unfold canAtP
  rw [planeMixedEdgeAt_transport N hN h q γ hq W₁ W₂ T hT x hx,
    planeMixedEdgeAt_transport N hN h q γ hq (dualRepG W₁) (dualRepG W₂) (dualEquiv W₁ W₂ T)
      (planeFrame_hTdual N hN h q γ hq W₁ W₂ T hT) y hy]
  have key := facePairingCan_twist hN (planeFrameEquiv N hN h q γ hq) (faceSplitting N h) (faceSplitting N (q * h * γ))
    W₁ W₂ T hT (planeFaceRadicalInput_det N h) (planeFaceRadicalInput_det N (q * h * γ)) (AGP hq) (alphaP_glConj hN hq)
    hconj (planeMixedEdgeAt N h W₁ ⟨x, hx⟩) (planeMixedEdgeAt N h (dualRepG W₁) ⟨y, hy⟩)
  rw [planeFrame_sign N hN h q γ hq, one_mul] at key
  exact key

end TernaryPeriodPolynomials.Argument.FrameInvariance
