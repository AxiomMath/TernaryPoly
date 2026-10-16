module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Corr
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.FrameLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.CuspConjNat

@[expose] public section


/-!
# Frame invariance of the canonical line pairing (generic coefficients)

Formalized by Claude Sonnet 5.5.

`canAt_transport`: for `h' = q h γ` (`q ∈ lineBorel`, `γ ∈ SL₃(ℤ)`), any coefficient modules `W₁` of the line group of `h`, `W₂` of that of `h'` related by `T : W₁ ≃ W₂` with `T (W₁(γ p γ⁻¹) v) = W₂(p) (T v)`,
and any mixed classes `x`, `y` (coefficients `W₁`, `W₁^*`), the transports of `x`, `y` are mixed and have the same canonical pairing: `canAt h' (Θx) (Θ'y) = canAt h x y`.  The orientation sign `det(φ_q) · det(A_G) = a² = 1`
(`lineFrame_sign`) is the product of the Koszul sign and the cup-form sign.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open CongruenceSubgroup TernaryPoly.RankTwoAugmentedFrames

section GenericRes

variable {E₁ E₂ L : Type} [Group E₁] [Group E₂] [Group L]
  {ext₁ : GroupExtension RadicalLattice E₁ L} {ext₂ : GroupExtension RadicalLattice E₂ L}
  (X : TwistEquiv ext₂ ext₁) (ρ₁ : Rep ℂ E₁) (ρ₂ : Rep ℂ E₂) (T : ρ₁ ≃ₗ[ℂ] ρ₂)
  (hT : ∀ (g : E₂) (v : ρ₁), T (ρ₁.ρ (X.θ g) v) = ρ₂.ρ g (T v))
  {K₁ K₂ : Type} [Group K₁] [Group K₂] (ι₁ : K₁ →* E₁) (ι₂ : K₂ →* E₂) (κ : K₂ →* K₁)
  (hκ : ∀ k, X.θ (ι₂ k) = ι₁ (κ k))

include hκ in
/-- If the restriction of `y` to `K₁` vanishes, so does the restriction of its transport to `K₂`, when `θ (K₂) ⊆ K₁`. -/
theorem res_h2X_eq_zero (y : groupCohomology.H2 ρ₁) (hy : twoCohomologyRestriction ι₁ ρ₁ y = 0) :
    twoCohomologyRestriction ι₂ ρ₂ (h2X X ρ₁ ρ₂ T hT y) = 0 := by
  have := SeedC3S4c.EdgeNat.restriction_h2Map X.θ.toMonoidHom ρ₁ ρ₂ T.toLinearMap hT ι₁ ι₂ κ hκ y
  rw [hy, map_zero] at this
  exact this

end GenericRes

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h q γ : SL(3, ℤ)) (hq : q ∈ lineBorel)
  (W₁ : Rep ℂ (gammaNQAt N h)) (W₂ : Rep ℂ (gammaNQAt N (q * h * γ))) (T : W₁ ≃ₗ[ℂ] W₂)
  (hT : ∀ (g : gammaNQAt N (q * h * γ)) (v : W₁),
    T (W₁.ρ ((lineFrameEquiv N hN h q γ hq).θ g) v) = W₂.ρ g (T v))

theorem h2X_eq_h2Map :
    h2X (lineFrameEquiv N hN h q γ hq) W₁ W₂ T hT =
      SeedC3S4c.EdgeNat.h2Map (lineFrameEquiv N hN h q γ hq).θ.toMonoidHom W₁ W₂ T.toLinearMap hT := rfl


theorem lineMixed_transport (x : groupCohomology.H2 W₁) (hx : x ∈ lineMixedAt N h W₁) :
    h2X (lineFrameEquiv N hN h q γ hq) W₁ W₂ T hT x ∈ lineMixedAt N (q * h * γ) W₂ := by
  refine (Submodule.mem_iInf _).2 fun F' => LinearMap.mem_ker.2 ?_
  set F : GL (Fin 2) ℚ := castGL (botRight q⁻¹) (botRight q) (botRight_inv_mul q hq).2 (botRight_inv_mul q hq).1 * F' with hF
  have hmem : ∀ k : lineFlagStab N (q * h * γ) F',
      (lineFrameEquiv N hN h q γ hq).θ k.1 ∈ lineFlagStab N h F := fun k =>
    (lineFlagStab_iff_chain N N h (q * h * γ) q γ hq rfl k.1.1 k.1.2 (γ * k.1.1 * γ⁻¹)
      ((lineFrameEquiv N hN h q γ hq).θ k.1).2 rfl F').mp k.2
  let κ : lineFlagStab N (q * h * γ) F' →* lineFlagStab N h F :=
    ((lineFrameEquiv N hN h q γ hq).θ.toMonoidHom.comp (lineFlagStab N (q * h * γ) F').subtype).codRestrict _ hmem
  exact res_h2X_eq_zero _ W₁ W₂ T hT (lineFlagStab N h F).subtype (lineFlagStab N (q * h * γ) F').subtype κ
    (fun _ => rfl) x (lineMixedAt_apply hx F)


include hT in
theorem lineFrame_hTdual : ∀ (g : gammaNQAt N (q * h * γ)) (φ : Module.Dual ℂ W₁),
    dualEquiv W₁ W₂ T ((dualRepG W₁).ρ ((lineFrameEquiv N hN h q γ hq).θ g) φ) = (dualRepG W₂).ρ g (dualEquiv W₁ W₂ T φ) :=
  FrameInvariance.hTdual (lineFrameEquiv N hN h q γ hq) W₁ W₂ T hT

variable [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂]

omit [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂] in
theorem mixedEdgeAt_transport (x : groupCohomology.H2 W₁) (hx : x ∈ lineMixedAt N h W₁) :
    mixedEdgeAt N (q * h * γ) W₂ ⟨h2X (lineFrameEquiv N hN h q γ hq) W₁ W₂ T hT x,
      lineMixed_transport N hN h q γ hq W₁ W₂ T hT x hx⟩ =
      cuspXi hN (alphaQ hN hq) (AG hq) (alphaQ_glConj hN hq) _ _
        (leviMap (lineFrameEquiv N hN h q γ hq) (lineFaceSplitting N h) (lineFaceSplitting N (q * h * γ)) W₁ W₂ T hT)
        (leviMap_equiv (lineFrameEquiv N hN h q γ hq) (lineFaceSplitting N h) (lineFaceSplitting N (q * h * γ)) W₁ W₂ T hT)
        (mixedEdgeAt N h W₁ ⟨x, hx⟩) := by
  apply Subtype.ext
  exact edge_kerMapX (lineFrameEquiv N hN h q γ hq) W₁ W₂ T hT (lineFaceSplitting N h)
    (lineFaceSplitting N (q * h * γ)) ⟨x, res_radical_of_lineMixedAt ⟨x, hx⟩⟩


/-- **Frame invariance of the canonical line pairing, for arbitrary coefficient modules.**  The transports of mixed classes `x`, `y` (coefficients `W₁`, `W₁^*`) along the frame change `h ↦ q h γ` are mixed and have
the same canonical pairing; the orientation sign `det(φ_q) · det(A_G) = a² = 1` does not appear. -/
theorem canAt_transport (hconj : CuspConjNat N hN) (x : groupCohomology.H2 W₁) (hx : x ∈ lineMixedAt N h W₁)
    (y : groupCohomology.H2 (dualRepG W₁)) (hy : y ∈ lineMixedAt N h (dualRepG W₁)) :
    canAt N (q * h * γ) hN W₂
        ⟨h2X (lineFrameEquiv N hN h q γ hq) W₁ W₂ T hT x, lineMixed_transport N hN h q γ hq W₁ W₂ T hT x hx⟩
        ⟨h2X (lineFrameEquiv N hN h q γ hq) (dualRepG W₁) (dualRepG W₂) (dualEquiv W₁ W₂ T)
          (lineFrame_hTdual N hN h q γ hq W₁ W₂ T hT) y,
          lineMixed_transport N hN h q γ hq (dualRepG W₁) (dualRepG W₂) (dualEquiv W₁ W₂ T)
            (lineFrame_hTdual N hN h q γ hq W₁ W₂ T hT) y hy⟩ =
      canAt N h hN W₁ ⟨x, hx⟩ ⟨y, hy⟩ := by
  unfold canAt
  rw [mixedEdgeAt_transport N hN h q γ hq W₁ W₂ T hT x hx,
    mixedEdgeAt_transport N hN h q γ hq (dualRepG W₁) (dualRepG W₂) (dualEquiv W₁ W₂ T)
      (lineFrame_hTdual N hN h q γ hq W₁ W₂ T hT) y hy]
  have key := facePairingCan_twist hN (lineFrameEquiv N hN h q γ hq) (lineFaceSplitting N h) (lineFaceSplitting N (q * h * γ))
    W₁ W₂ T hT (lineFaceRadicalInput_det N h) (lineFaceRadicalInput_det N (q * h * γ)) (AG hq) (alphaQ_glConj hN hq)
    hconj (mixedEdgeAt N h W₁ ⟨x, hx⟩) (mixedEdgeAt N h (dualRepG W₁) ⟨y, hy⟩)
  rw [lineFrame_sign N hN h q γ hq, one_mul] at key
  exact key

end TernaryPeriodPolynomials.Argument.FrameInvariance
