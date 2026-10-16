module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentClass

@[expose] public section


/-!
# The rotation and the inverse transpose carry parabolic classes to parabolic classes

The Kostant coordinate at the identity plane is the rotation `g(x, y) ↦ g(-y, x)` of the binary
coordinate, and the Levi element `diag(γ, 1)` of the line is the image of the Levi element
`diag(γ^{-T}, 1)` of the plane.  So the one-cocycle of `GL₂(ℤ)` attached to the dual plane is the
pullback of a one-cocycle `F` along the involution `invT γ = γ^{-T}`, followed by the rotation:

  `Z γ = - rot (F (invT γ))`.

The rotation intertwines `ρ(γ)` and `ρ(invT γ)` on `Sym^{n+1} ⊗ det^τ` when `n` is odd
(`swap_rho`).  Hence the class of `Z` is nonzero iff the class of `F` is, and `Z` is a parabolic
cocycle when `F` is: the lower unipotent matrix `invT T = S T S⁻¹` is conjugate to `T` by `S`, and a
cocycle which is a coboundary at `T` is a coboundary at every conjugate of `T`.

* `swap_rho`: the intertwining of the rotation.
* `swapPullback_mem_parabolicCocycles`: parabolicity of the transported cocycle.
* `swapPullback_projectH1_ne_zero`: non-vanishing of the transported class.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (invT mul_invT_transpose invT_inv_val map_mul_transpose binarySwap binarySwap_injective
    binarySwapEquiv binarySwap_homogeneousAction homogeneousAction_even_twist)
open TernaryPeriodPolynomials.BoundaryDuality.CocycleBridge (IsCocycle)

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident

open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne

/-! ### The involution `invT` -/

/-- The inverse transpose is an involution of `GL₂(ℤ)`. -/
theorem invT_invT (γ : GL2Z) : invT (invT γ) = γ := by
  apply Units.ext
  change (((invT γ)⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)ᵀ = (γ : Matrix (Fin 2) (Fin 2) ℤ)
  rw [invT_inv_val, Matrix.transpose_transpose]

/-- The matrix `invT γ` times the transpose of `γ` is the identity. -/
theorem invT_mul_transpose (γ : GL2Z) :
    ((invT γ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ)ᵀ = 1 := by
  have h := mul_invT_transpose (invT γ)
  rwa [invT_invT] at h

/-- `invT T · S = S · T`: the lower unipotent matrix `invT T` is the conjugate `S T S⁻¹`. -/
theorem invT_T_mul_S :
    invT (toGL ModularGroup.T) * toGL ModularGroup.S = toGL ModularGroup.S * toGL ModularGroup.T := by
  have h : (invT (toGL ModularGroup.T))⁻¹ * (toGL ModularGroup.S * toGL ModularGroup.T) =
      toGL ModularGroup.S := by
    apply Units.ext
    rw [Units.val_mul, invT_inv_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toGL, ModularGroup.coe_S, ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  exact (inv_mul_eq_iff_eq_mul.mp h).symm

/-! ### The rotation intertwines `ρ(γ)` and `ρ(invT γ)` -/

/-- **The rotation intertwines `ρ(γ)` and `ρ(invT γ)`** on `Sym^{n+1} ⊗ det^τ` for odd `n`. -/
theorem swap_rho {n : ℕ} (hn : Odd n) (τ : ℤ) (γ : GL2Z) (v : arithmeticBinaryRep (n + 1) τ) :
    binarySwap (n + 1) ((arithmeticBinaryRep (n + 1) τ).ρ γ v) =
      (arithmeticBinaryRep (n + 1) τ).ρ (invT γ) (binarySwap (n + 1) v) := by
  have hev : Even ((((n + 1 : ℕ) : ℤ) - τ) - τ) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨(k : ℤ) + 1 - τ, by omega⟩
  change binarySwap (n + 1) (Binary.homogeneousAction (n + 1) τ
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) γ) v) =
    Binary.homogeneousAction (n + 1) τ
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (invT γ)) (binarySwap (n + 1) v)
  rw [binarySwap_homogeneousAction (n + 1) τ
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (invT γ))
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) γ)
    (map_mul_transpose (invT γ) γ (invT_mul_transpose γ)) v,
    homogeneousAction_even_twist (n + 1) (((n + 1 : ℕ) : ℤ) - τ) τ hev (invT γ)]

/-- The rotation as an endomorphism of the coefficient module `Sym^{n+1} ⊗ det^τ`. -/
def swA (n : ℕ) (τ : ℤ) : arithmeticBinaryRep (n + 1) τ →ₗ[ℂ] arithmeticBinaryRep (n + 1) τ :=
  binarySwap (n + 1)

theorem swA_injective (n : ℕ) (τ : ℤ) : Function.Injective (swA n τ) :=
  binarySwap_injective (n + 1)

/-! ### Parabolic cocycles -/

local notation "Tm" => toGL ModularGroup.T
local notation "Sm" => toGL ModularGroup.S

/-- **The transported cocycle is parabolic.**  If `F` is a parabolic one-cocycle and
`Z γ = - rot (F (invT γ))`, then `Z` is a parabolic one-cocycle. -/
theorem swapPullback_mem_parabolicCocycles {n : ℕ} (hn : Odd n) (τ : ℤ)
    {F Z : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) τ)}
    (hF : F ∈ parabolicCocycles (arithmeticBinaryRep (n + 1) τ))
    (hZ : ∀ γ, Z γ = -binarySwap (n + 1) (F (invT γ))) :
    Z ∈ parabolicCocycles (arithmeticBinaryRep (n + 1) τ) := by
  rw [mem_parabolicCocycles_iff] at hF ⊢
  obtain ⟨u₀, hu₀⟩ := hF
  have hc := isCocycle_cocycleInclusion (arithmeticBinaryRep (n + 1) τ) F
  have hρ : (arithmeticBinaryRep (n + 1) τ).ρ Sm ((arithmeticBinaryRep (n + 1) τ).ρ Tm u₀) =
      (arithmeticBinaryRep (n + 1) τ).ρ (invT Tm)
        ((arithmeticBinaryRep (n + 1) τ).ρ Sm u₀) := by
    calc (arithmeticBinaryRep (n + 1) τ).ρ Sm ((arithmeticBinaryRep (n + 1) τ).ρ Tm u₀)
        = (arithmeticBinaryRep (n + 1) τ).ρ (Sm * Tm) u₀ := by
          rw [map_mul, Module.End.mul_apply]
      _ = (arithmeticBinaryRep (n + 1) τ).ρ (invT Tm * Sm) u₀ := by rw [invT_T_mul_S]
      _ = (arithmeticBinaryRep (n + 1) τ).ρ (invT Tm) ((arithmeticBinaryRep (n + 1) τ).ρ Sm u₀) := by
          rw [map_mul, Module.End.mul_apply]
  have hLS : cocycleInclusion (arithmeticBinaryRep (n + 1) τ) F (invT Tm * Sm) =
      cocycleInclusion (arithmeticBinaryRep (n + 1) τ) F (Sm * Tm) :=
    congrArg (cocycleInclusion (arithmeticBinaryRep (n + 1) τ) F) invT_T_mul_S
  rw [hc (invT Tm) Sm, hc Sm Tm, hu₀] at hLS
  obtain ⟨w, hw⟩ : ∃ w : arithmeticBinaryRep (n + 1) τ,
      w = (arithmeticBinaryRep (n + 1) τ).ρ Sm u₀ -
        cocycleInclusion (arithmeticBinaryRep (n + 1) τ) F Sm := ⟨_, rfl⟩
  have key : cocycleInclusion (arithmeticBinaryRep (n + 1) τ) F (invT Tm) =
      (arithmeticBinaryRep (n + 1) τ).ρ (invT Tm) w - w := by
    have hLS' := eq_sub_of_add_eq hLS
    rw [map_sub] at hLS'
    rw [hw, map_sub, hLS', hρ]
    abel
  have e1 : cocycleInclusion (arithmeticBinaryRep (n + 1) τ) Z Tm =
      -swA n τ (cocycleInclusion (arithmeticBinaryRep (n + 1) τ) F (invT Tm)) := hZ Tm
  have e2 : swA n τ ((arithmeticBinaryRep (n + 1) τ).ρ (invT Tm) w) =
      (arithmeticBinaryRep (n + 1) τ).ρ Tm (swA n τ w) :=
    (swap_rho hn τ (invT Tm) w).trans (by rw [invT_invT]; rfl)
  refine ⟨-(swA n τ w), ?_⟩
  rw [e1, key, map_sub, e2, map_neg]
  abel

/-- **The class of the transported cocycle is nonzero** when the class of `F` is nonzero, for
`Z γ = - rot (F (invT γ))`. -/
theorem swapPullback_projectH1_ne_zero {n : ℕ} (hn : Odd n) (τ : ℤ)
    {F Z : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) τ)}
    (hZ : ∀ γ, Z γ = -binarySwap (n + 1) (F (invT γ)))
    (hF : projectH1 (arithmeticBinaryRep (n + 1) τ) F ≠ 0) :
    projectH1 (arithmeticBinaryRep (n + 1) τ) Z ≠ 0 := by
  intro h0
  apply hF
  rw [projectH1_eq_zero_iff] at h0 ⊢
  obtain ⟨u, hu⟩ := h0
  obtain ⟨s, hs⟩ : ∃ s : arithmeticBinaryRep (n + 1) τ, swA n τ s = u :=
    (binarySwapEquiv (n + 1)).surjective u
  refine ⟨-s, fun δ => ?_⟩
  apply swA_injective n τ
  have e1 : swA n τ (F δ) = -(Z (invT δ)) := by
    have h : Z (invT δ) = -swA n τ (F (invT (invT δ))) := hZ (invT δ)
    rw [invT_invT] at h
    rw [h, neg_neg]
  have hu' : Z (invT δ) = (arithmeticBinaryRep (n + 1) τ).ρ (invT δ) u - u := hu (invT δ)
  have e4 : (arithmeticBinaryRep (n + 1) τ).ρ (invT δ) u =
      swA n τ ((arithmeticBinaryRep (n + 1) τ).ρ δ s) := by
    rw [← hs]
    exact (swap_rho hn τ δ s).symm
  change swA n τ (F δ) = swA n τ ((arithmeticBinaryRep (n + 1) τ).ρ δ (-s) - -s)
  rw [e1, hu', e4, ← hs]
  simp only [map_sub, map_neg]
  abel

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident

end
