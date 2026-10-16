module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadOdd
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge2
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddTilde

@[expose] public section


/-!
# The comparison of the coefficients intertwines the whole `GL₂(ℚ)`-action

The comparison map `E = σ_var ∘ rot ∘ Sym(σ) ∘ Φ⁻¹` of the coefficients `Sym^{n+1} ⊗ det⁻¹` of the
good-plane edge with the coefficients of the odd-degree bridge (it is `IdentBad.planeComparison`)
satisfies, for every `h ∈ GL₂(ℚ)`,

  `E ∘ σ(h) = A_{n+2}(tilde h) ∘ E`,   `A_τ = Sym^{n+1} ⊗ det^τ`,  `tilde h = δ (h⁻¹)ᵀ δ⁻¹`

(`planeE_rho_tilde`).  For `h ∈ Γ₁'(3)` this is the equivariance used by the bridge (the twists
`n + 2` and `-1` agree on determinants `±1` since `n` is odd); for the Hecke representatives
(determinant `p`) it records the scalar `p^{n+3}` by which the twists differ.

The proof composes the intertwining of the rotation `rot` (`binarySwap_homogeneousAction`) and of
the exchange of variables (`binarySwapVar_action_twist`) with the group identity
`s · (s c(δ)) · invT(g) · (s c(δ))⁻¹ · s⁻¹ = c(δ) invT(g) c(δ)⁻¹`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddIntertwine

open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (binarySwap binarySwapVar swapUnit swapUnit_mul_self swapZ swapInt binarySwapVar_action_twist
    binarySwap_homogeneousAction swap01)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddTilde
  (invTG invTG_val invTG_mul invTG_one map_invTG tilde invTQ)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2 (PhiInv)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame (del del_val del_inv_val)

variable {n : ℕ}

/-- **The comparison map** `E = σ_var ∘ rot ∘ Sym(σ) ∘ Φ⁻¹` (the definition of
`BadIdentPlane.planeComparison`). -/
def planeE (n : ℕ) : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (binarySwapVar (n + 1)).comp ((binarySwap (n + 1)).comp
    ((Binary.homogeneousAction (n + 1) (-1)
      (GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ)).comp (PhiInv n)))

section Matrices

/-- The exchange matrix over `ℂ` is the image of the integral exchange matrix. -/
theorem swapZ_complex : GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ = swapUnit := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapZ, swapInt, swapUnit, swap01, GeneralLinearGroup.map_apply]

/-- The exchange matrix is its own inverse transpose. -/
theorem invTG_swapUnit : invTG swapUnit = swapUnit := by
  have hinv : swapUnit⁻¹ = swapUnit := inv_eq_of_mul_eq_one_right swapUnit_mul_self
  apply Units.ext
  rw [invTG_val, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapUnit, swap01, Matrix.transpose_apply]

/-- The inverse transpose of `δ⁻¹` is `δ`. -/
theorem invTG_del_inv : invTG (del⁻¹ : GL (Fin 2) ℚ) = del := by
  apply Units.ext
  rw [invTG_val, inv_inv, del_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

/-- The change of coefficients `ℚ → ℂ` on `GL₂`. -/
abbrev cQ : GL (Fin 2) ℚ →* GL (Fin 2) ℂ := GeneralLinearGroup.map (algebraMap ℚ ℂ)

/-- The matrix `D = σ δ⁻¹` of the comparison map. -/
def Dmat : GL (Fin 2) ℂ := swapUnit * cQ del⁻¹

/-- The conjugating matrix of the comparison map. -/
def Ymat (g : GL (Fin 2) ℂ) : GL (Fin 2) ℂ := swapUnit * invTG (Dmat * g) * swapUnit⁻¹

/-- **The key identity of matrices**: `Y(c h) · Y(1)⁻¹ = c (tilde h)`. -/
theorem Ymat_div (h : GL (Fin 2) ℚ) : Ymat (cQ h) * (Ymat 1)⁻¹ = cQ (tilde h) := by
  have hD : swapUnit * invTG Dmat = cQ del := by
    rw [Dmat, invTG_mul, invTG_swapUnit, ← map_invTG (algebraMap ℚ ℂ), invTG_del_inv,
      ← mul_assoc, swapUnit_mul_self, one_mul]
  have e : Ymat (cQ h) * (Ymat 1)⁻¹ =
      (swapUnit * invTG Dmat) * invTG (cQ h) * (swapUnit * invTG Dmat)⁻¹ := by
    unfold Ymat
    rw [invTG_mul, mul_one]
    group
  rw [e, hD, ← map_invTG (algebraMap ℚ ℂ)]
  show _ = cQ (del * invTG h * del⁻¹)
  rw [map_mul, map_mul, map_inv]

end Matrices

section Intertwine

/-- The twist of the action after the rotation. -/
abbrev tw (n : ℕ) : ℤ := ((n + 1 : ℕ) : ℤ) - (-1)

theorem invTG_rel (K : GL (Fin 2) ℂ) :
    ((invTG K : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * (K : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 1 := by
  rw [invTG_val, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem planeE_apply (v : Binary.HomogeneousPoly (n + 1)) :
    planeE n v = binarySwapVar (n + 1) (binarySwap (n + 1)
      (Binary.homogeneousAction (n + 1) (-1) Dmat v)) := by
  have hs : Binary.homogeneousAction (n + 1) (-1) Dmat v =
      Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ)
        (PhiInv n v) := by
    rw [Dmat, swapZ_complex, map_mul, Module.End.mul_apply]
    rfl
  rw [hs]
  rfl

theorem planeE_act (g : GL (Fin 2) ℂ) (v : Binary.HomogeneousPoly (n + 1)) :
    planeE n (Binary.homogeneousAction (n + 1) (-1) g v) =
      Binary.homogeneousAction (n + 1) (tw n) (Ymat g)
        (binarySwapVar (n + 1) (binarySwap (n + 1) v)) := by
  have hmul : Binary.homogeneousAction (n + 1) (-1) Dmat
      (Binary.homogeneousAction (n + 1) (-1) g v) =
      Binary.homogeneousAction (n + 1) (-1) (Dmat * g) v := by
    rw [map_mul, Module.End.mul_apply]
  rw [planeE_apply, hmul,
    binarySwap_homogeneousAction (n + 1) (-1) (invTG (Dmat * g)) (Dmat * g)
      (invTG_rel (Dmat * g)) v,
    binarySwapVar_action_twist]
  rfl

/-- **The comparison map intertwines the `GL₂(ℚ)`-action**: `E σ(h) = A_{n+2}(tilde h) E`. -/
theorem planeE_rho_tilde (h : GL (Fin 2) ℚ) (v : Binary.HomogeneousPoly (n + 1)) :
    planeE n (Binary.homogeneousAction (n + 1) (-1) (cQ h) v) =
      Binary.homogeneousAction (n + 1) (tw n) (cQ (tilde h)) (planeE n v) := by
  rw [planeE_act]
  have hW : binarySwapVar (n + 1) (binarySwap (n + 1) v) =
      Binary.homogeneousAction (n + 1) (tw n) (Ymat 1)⁻¹ (planeE n v) := by
    have h0 := planeE_act (n := n) 1 v
    rw [map_one, Module.End.one_apply] at h0
    rw [h0]
    have h1 : Binary.homogeneousAction (n + 1) (tw n) (Ymat 1)⁻¹
        (Binary.homogeneousAction (n + 1) (tw n) (Ymat 1)
          (binarySwapVar (n + 1) (binarySwap (n + 1) v))) =
        binarySwapVar (n + 1) (binarySwap (n + 1) v) := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    exact h1.symm
  rw [hW]
  have h2 : Binary.homogeneousAction (n + 1) (tw n) (Ymat (cQ h))
      (Binary.homogeneousAction (n + 1) (tw n) (Ymat 1)⁻¹ (planeE n v)) =
      Binary.homogeneousAction (n + 1) (tw n) (Ymat (cQ h) * (Ymat 1)⁻¹) (planeE n v) := by
    rw [map_mul, Module.End.mul_apply]
  rw [h2, Ymat_div]

end Intertwine

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddIntertwine

end
