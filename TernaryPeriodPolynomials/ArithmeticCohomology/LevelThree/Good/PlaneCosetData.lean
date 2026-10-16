module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneCosets

@[expose] public section


/-!
# Definitions of the local `T_p`-cosets at the good plane

For a prime `p ≠ 3` let `ε_p = ±1 ≡ p (mod 3)` (`LevelThreeCosets.signP`) and let `α_j` be the
`Γ₁'(3)`-Hecke representatives `α_j = [[1, j], [0, p]]`, `α_∞ = ε_p [[p, 0], [0, 1]]` of
`LevelThreeCosets`. In the block coordinates of the good plane (`GoodPlaneFrame`) the Levi group
`Γ₁'(3)` acts through `κ(m) = δ⁻¹ m δ`, so the relevant Hecke matrices are `δ⁻¹ α_j δ`, and the
matrices `B_j = p (δ⁻¹ α_j δ)⁻¹` are explicitly

`B_∞ = ε_p · diag(1, p)` and `B_i = [[p, -3i], [0, 1]]`.

The radical lattice `ℤ²` is split modulo `B_j ℤ²` by the representatives `w_{∞, r} = (0, r)` and
`w_{i, r} = (r, 0)` (`wint`, `repIdx`, `quotVec`). The `1 + p(p+1)` elements
`σ₀ = P(0, 1, εp)` (`εp = ±p ≡ 1 mod 3`) and `s_{j,r} = P(w_{j,r}, B_j, 1)` (`sExpl`) are the local
coset representatives at the good plane; the identity-plane analogue is
`IdentityPlaneCosets.sExpl`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneCosetData

open TernaryPeriodPolynomials.Spectral
open PlaneCoordinates
open IdentityPlaneCosets (icast epsU p_ne_zero)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets (signP signP_mul_self)

variable (p : Nat.Primes)

/-- `B_∞ = ε_p diag(1, p)`, `B_i = [[p, -3i], [0, 1]]`. -/
def Bmat : Option (Fin p.val) → Matrix (Fin 2) (Fin 2) ℚ
  | none => !![((signP p : ℤ) : ℚ), 0; 0, ((signP p : ℤ) : ℚ) * (p.val : ℚ)]
  | some i => !![(p.val : ℚ), -(3 * (i.val : ℚ)); 0, 1]

theorem Bmat_det (j : Option (Fin p.val)) : (Bmat p j).det = p.val := by
  have hs : ((signP p : ℤ) : ℚ) * ((signP p : ℤ) : ℚ) = 1 := by
    exact_mod_cast signP_mul_self p
  cases j with
  | none =>
    simp only [Bmat, Matrix.det_fin_two_of]
    linear_combination (p.val : ℚ) * hs
  | some i =>
    simp only [Bmat, Matrix.det_fin_two_of]
    ring

/-- `B_j` in `GL₂(ℚ)`. -/
def BG (j : Option (Fin p.val)) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero (Bmat p j) (by rw [Bmat_det]; exact p_ne_zero p)

theorem BG_val (j : Option (Fin p.val)) : (BG p j).val = Bmat p j := rfl

/-- The representative index of `b` modulo `B_j ℤ²`. -/
def repIdx : Option (Fin p.val) → ℤ × ℤ → Fin p.val
  | none, b => ⟨(b.2 % (p.val : ℤ)).toNat, by
      have h1 := Int.emod_nonneg b.2 (by exact_mod_cast p.property.ne_zero : (p.val : ℤ) ≠ 0)
      have h2 := Int.emod_lt_of_pos b.2 (by exact_mod_cast p.property.pos : (0 : ℤ) < p.val)
      omega⟩
  | some i, b => ⟨((b.1 + 3 * i.val * b.2) % (p.val : ℤ)).toNat, by
      have h1 := Int.emod_nonneg (b.1 + 3 * i.val * b.2)
        (by exact_mod_cast p.property.ne_zero : (p.val : ℤ) ≠ 0)
      have h2 := Int.emod_lt_of_pos (b.1 + 3 * i.val * b.2)
        (by exact_mod_cast p.property.pos : (0 : ℤ) < p.val)
      omega⟩

/-- The representatives `w_{∞,r} = (0, r)`, `w_{i,r} = (r, 0)` of `ℤ² / B_j ℤ²`. -/
def wint : Option (Fin p.val) → Fin p.val → ℤ × ℤ
  | none, r => (0, r.val)
  | some _, r => (r.val, 0)

/-- The integral vector `B_j⁻¹ (b - w_{j, rep b})`. -/
def quotVec : Option (Fin p.val) → ℤ × ℤ → ℤ × ℤ
  | none, b => ((signP p : ℤ) * b.1, (signP p : ℤ) * (b.2 / (p.val : ℤ)))
  | some i, b => ((b.1 + 3 * i.val * b.2) / (p.val : ℤ), b.2)

/-- The index type `{σ₀} ⊔ {(j, r)}`. -/
abbrev SIdx := Option (Option (Fin p.val) × Fin p.val)

/-- The explicit elements `σ₀ = P(0, 1, εp)` and `s_{j,r} = P(w_{j,r}, B_j, 1)`. -/
def sExpl : SIdx p → RationalGL3
  | none => P 0 1 (epsU p)
  | some (j, r) => P (icast (wint p j r)) (BG p j) 1

end TernaryPeriodPolynomials.LevelThree.GoodPlaneCosetData
