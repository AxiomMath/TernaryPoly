module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Isotropy
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.InvolutionLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Apolar
public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Main
public import TernaryPeriodPolynomials.Building.FreeResolution.Main

@[expose] public section



/-! The dual coefficient system is `trivialCharacter`, so no `InducingData` is available; the two
library lemmas that are stated for a general `InducingData n` but only ever use its `.chi` field
(`cupTwoTwo_mem` and, through it, `CupProductExactness`) are re-derived here directly for
`trivialCharacter`. Everything else (`cochain_triple`, `isCocycleTwo_of_mem`,
`differentialFourRaw_cupTwoTwo`, `dualPairing_invariant`, `dualInvolution_mem_rationalLevel`,
`globalTopVanishing_of_topVanishing`, `topVanishing_rationalLevel`) is already fully general. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality

namespace TernaryPeriodPolynomials.Argument.Classification

/-- `cupTwoTwo_mem` specialized to `trivialCharacter`: the twisted cup product of two global
two-cocycles of the trivial-character coefficient system is an invariant scalar four-cochain. -/
theorem cupTwoTwo_mem_trivial {n : ℕ} (φ : RationalGL3 →* RationalGL3)
    (level : ∀ g ∈ rationalLevel, φ g ∈ rationalLevel)
    (B : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ)
    (invariant : ∀ g ∈ rationalLevel, ∀ v w,
      B (rationalCoefficientComponent n trivialCharacter g v)
        (rationalCoefficientComponent n trivialCharacter (φ g) w) = B v w)
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    cupTwoTwo B φ c.val.val c'.val.val ∈ cochains rationalLevel scalarTrivial 4 := by
  intro γ x
  have dual : φ γ.val ∈ rationalLevel := level γ.val γ.property
  change B (c.val.val ![γ.val * x 0, γ.val * x 1, γ.val * x 2])
      (c'.val.val ![φ (γ.val * x 2), φ (γ.val * x 3), φ (γ.val * x 4)]) =
    B (c.val.val ![x 0, x 1, x 2]) (c'.val.val ![φ (x 2), φ (x 3), φ (x 4)])
  rw [map_mul, map_mul, map_mul, cochain_triple c.val γ,
    cochain_triple c'.val ⟨φ γ.val, dual⟩]
  exact invariant γ.val γ.property _ _

/-- A `scalarTrivial` three-cochain extended constantly over any `RationalGL3`-set is a
`functionRepresentation scalarTrivial`-cochain. -/
theorem constantCochainMem {X : Type} [MulAction RationalGL3 X]
    (θ : (Fin 4 → RationalGL3) → ℂ) (θmem : θ ∈ cochains rationalLevel scalarTrivial 3) :
    (fun x (_ : X) => θ x) ∈ cochains rationalLevel (functionRepresentation scalarTrivial X) 3 := by
  intro γ x
  funext F
  exact θmem γ x

theorem face_pairing_stokes (n : ℕ)
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w : EdgeCochains n trivialCharacter 1)
    (_hw : ∀ x e, c.val.val x = differentialOneRaw w.val x e)
    (γP : (Fin 4 → RationalGL3) → Flags .plane → ℂ)
    (hγP : γP ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 3)
    (hdγP : ∀ x P, differentialThreeRaw γP x P =
      dualPairing n (c.val.val ![x 0, x 1, x 2])
        (c'.val.val ![dualInvolution (x 2), dualInvolution (x 3), dualInvolution (x 4)]))
    (γQ : (Fin 4 → RationalGL3) → Flags .line → ℂ)
    (hγQ : γQ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3)
    (hdγQ : ∀ x F, differentialThreeRaw γQ x F =
      dualPairing n (c.val.val ![x 0, x 1, x 2])
        (c'.val.val ![dualInvolution (x 2), dualInvolution (x 3), dualInvolution (x 4)])) :
    BoundaryExact (fun x e =>
      (dualPairing n (w.val ![x 0, x 1] e)
          (c'.val.val ![dualInvolution (x 1), dualInvolution (x 2), dualInvolution (x 3)]) -
        γP x (endpoint .plane e)) -
      (dualPairing n (w.val ![x 0, x 1] e)
          (c'.val.val ![dualInvolution (x 1), dualInvolution (x 2), dualInvolution (x 3)]) -
        γQ x (endpoint .line e))) := by
  -- `H⁴(Γ, ℂ) = 0` unconditionally, for the trivial character.
  have top : GlobalTopVanishing :=
    TernaryPeriodPolynomials.TopVanishing.globalTopVanishing_of_topVanishing
      TernaryPeriodPolynomials.FreeResolution.topVanishing_rationalLevel
  have hlevel : ∀ g ∈ rationalLevel, dualInvolution g ∈ rationalLevel :=
    fun _ membership => dualInvolution_mem_rationalLevel membership
  have hinvariant : ∀ g ∈ rationalLevel, ∀ v w : HomogeneousPoly n,
      dualPairing n (rationalCoefficientComponent n trivialCharacter g v)
        (rationalCoefficientComponent n trivialCharacter (dualInvolution g) w) =
        dualPairing n v w :=
    fun g _ v w => dualPairing_invariant n trivialCharacter g v w
  -- The invariant scalar four-cocycle `c ⌣ c'^φ` is a coboundary of a scalar three-cochain `θ`.
  obtain ⟨θ, θmem, θprimitive⟩ :=
    top (cupTwoTwo (dualPairing n) dualInvolution c.val.val c'.val.val)
      (cupTwoTwo_mem_trivial dualInvolution hlevel (dualPairing n) hinvariant c c')
      (differentialFourRaw_cupTwoTwo (dualPairing n) dualInvolution
        (isCocycleTwo_of_mem c) (isCocycleTwo_of_mem c'))
  -- `θ` has the same coboundary as `γP` and `γQ` (both equal the cup-product value, by
  -- `hdγP`/`hdγQ` and `θprimitive`, after unfolding `cupTwoTwo`).
  have θeqP : ∀ x P, differentialThreeRaw θ x = differentialThreeRaw γP x P := by
    intro x P
    rw [θprimitive x, hdγP x P]
    rfl
  have θeqQ : ∀ x F, differentialThreeRaw θ x = differentialThreeRaw γQ x F := by
    intro x F
    rw [θprimitive x, hdγQ x F]
    rfl
  refine ⟨0, (fun x (_ : Flags .plane) => θ x) - γP, (fun x (_ : Flags .line) => θ x) - γQ,
    sub_mem (constantCochainMem θ θmem) hγP, sub_mem (constantCochainMem θ θmem) hγQ,
    ?_, ?_, ?_⟩
  · intro x
    funext P
    have expand : differentialThreeRaw ((fun x (_ : Flags .plane) => θ x) - γP) x P =
        differentialThreeRaw θ x - differentialThreeRaw γP x P := by
      simp only [differentialThreeRaw, Pi.sub_apply, Pi.add_apply]
      ring
    rw [expand, θeqP x P, sub_self]
    rfl
  · intro x
    funext F
    have expand : differentialThreeRaw ((fun x (_ : Flags .line) => θ x) - γQ) x F =
        differentialThreeRaw θ x - differentialThreeRaw γQ x F := by
      simp only [differentialThreeRaw, Pi.sub_apply, Pi.add_apply]
      ring
    rw [expand, θeqQ x F, sub_self]
    rfl
  · intro x e
    simp only [map_zero, Pi.zero_apply, Pi.sub_apply]
    ring

end TernaryPeriodPolynomials.Argument.Classification
