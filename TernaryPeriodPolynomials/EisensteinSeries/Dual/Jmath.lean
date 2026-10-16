module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.Rational
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.Flags

@[expose] public section


open scoped MatrixGroups
open Matrix

/-!
# The involution `ȷ(g) = J (g⁻¹)ᵗ J` of `SL₃(ℤ)` exchanging the cusps `P` and `Q`

Formalized by Claude Sonnet 5.5.

Paper: "The dual series and the boundary relation": `J` is the antidiagonal permutation matrix and
`ȷ(g) = J (g⁻¹)ᵗ J`; it "exchanges `P`, `Q`".  With the anti-transpose `rt M = J Mᵗ J` of `GammaNFaces.Rational`, `ȷ(g) = (rt g)⁻¹`
(`jmath`), an involutive automorphism (`jmathEquiv`).  It preserves `Γ(N)` (`jmath_mem_gammaN`), exchanges the plane and line
stabilizers and the groups `Γ(N) ∩ P(ℤ)`, `Γ(N) ∩ Q(ℤ)` (`jmath_mem_gammaNQ_iff`, `jmath_mem_gammaNP_iff`) and their conjugates
`Γ_{h⁻¹Ph}`, `Γ_{h⁻¹Qh}` (`jmath_mem_gammaNQAt_iff`, `jmath_mem_gammaNPAt_iff`: `ȷ` carries the cusp `h` to the cusp `ȷ(h)`), and
preserves the Borel group and the flag groups `Γ_B` (`jmath_mem_gammaNBAt_iff`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces

/-- **The involution `ȷ(g) = J (g⁻¹)ᵗ J`** of `SL₃(ℤ)` (`J` the antidiagonal permutation matrix): since `rt g = J gᵗ J` is the
anti-transpose, `ȷ(g) = (rt g)⁻¹`. -/
def jmath (A : SL(3, ℤ)) : SL(3, ℤ) := (rtSL A)⁻¹

theorem jmath_mul (A B : SL(3, ℤ)) : jmath (A * B) = jmath A * jmath B := by
  unfold jmath
  rw [rtSL_mul, _root_.mul_inv_rev]

theorem jmath_one : jmath 1 = 1 := by
  unfold jmath
  rw [rtSL_one, inv_one]

theorem jmath_inv (A : SL(3, ℤ)) : jmath A⁻¹ = (jmath A)⁻¹ := by
  unfold jmath
  rw [rtSL_inv]

theorem jmath_jmath (A : SL(3, ℤ)) : jmath (jmath A) = A := by
  unfold jmath
  rw [rtSL_inv, inv_inv, rtSL_rtSL]

/-- `ȷ` as an automorphism of `SL₃(ℤ)`. -/
def jmathEquiv : SL(3, ℤ) ≃* SL(3, ℤ) where
  toFun := jmath
  invFun := jmath
  left_inv := jmath_jmath
  right_inv := jmath_jmath
  map_mul' := jmath_mul

@[simp] theorem jmathEquiv_apply (A : SL(3, ℤ)) : jmathEquiv A = jmath A := rfl

/-- The matrix of `ȷ(g)` is `J (g⁻¹)ᵗ J = rt (g⁻¹)`. -/
theorem coe_jmath (A : SL(3, ℤ)) :
    ((jmath A : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = rt ((A⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) := by
  unfold jmath
  rw [← rtSL_inv]
  rfl

theorem jmath_mem_gammaN {N : ℕ} {A : SL(3, ℤ)} : jmath A ∈ gammaN N ↔ A ∈ gammaN N := by
  have key : ∀ {B : SL(3, ℤ)}, B ∈ gammaN N → jmath B ∈ gammaN N := fun {B} hB =>
    (gammaN N).inv_mem (rtSL_mem_gammaN hB)
  exact ⟨fun h => by simpa [jmath_jmath] using key h, key⟩

theorem rtSL_jmath (A : SL(3, ℤ)) : rtSL (jmath A) = A⁻¹ := by
  unfold jmath
  rw [← rtSL_inv, rtSL_rtSL]

theorem rtSL_mem_borelStab_iff {A : SL(3, ℤ)} : rtSL A ∈ borelStab ↔ A ∈ borelStab := by
  constructor <;> rintro ⟨h0, h1, h2⟩ <;>
    exact ⟨by simpa [coe_rtSL, rt, Fin.rev] using h2, by simpa [coe_rtSL, rt, Fin.rev] using h1,
      by simpa [coe_rtSL, rt, Fin.rev] using h0⟩

theorem jmath_mem_lineStab_iff {A : SL(3, ℤ)} : jmath A ∈ lineStab ↔ A ∈ planeStab := by
  rw [lineStab_iff_rtSL, rtSL_jmath, inv_mem_iff]

theorem jmath_mem_planeStab_iff {A : SL(3, ℤ)} : jmath A ∈ planeStab ↔ A ∈ lineStab := by
  have := jmath_mem_lineStab_iff (A := jmath A)
  rw [jmath_jmath] at this
  exact this.symm

theorem jmath_mem_borelStab_iff {A : SL(3, ℤ)} : jmath A ∈ borelStab ↔ A ∈ borelStab := by
  unfold jmath
  rw [inv_mem_iff, rtSL_mem_borelStab_iff]

theorem jmath_mem_gammaNQ_iff {N : ℕ} {A : SL(3, ℤ)} : jmath A ∈ gammaNQ N ↔ A ∈ gammaNP N := by
  unfold gammaNQ gammaNP
  rw [Subgroup.mem_inf, Subgroup.mem_inf, jmath_mem_gammaN, jmath_mem_lineStab_iff]

theorem jmath_mem_gammaNP_iff {N : ℕ} {A : SL(3, ℤ)} : jmath A ∈ gammaNP N ↔ A ∈ gammaNQ N := by
  have := jmath_mem_gammaNQ_iff (N := N) (A := jmath A)
  rw [jmath_jmath] at this
  exact this.symm

theorem jmath_mem_gammaNB_iff {N : ℕ} {A : SL(3, ℤ)} : jmath A ∈ gammaNB N ↔ A ∈ gammaNB N := by
  unfold gammaNB
  rw [Subgroup.mem_inf, Subgroup.mem_inf, jmath_mem_gammaN, jmath_mem_borelStab_iff]

/-- The plane group of the cusp `h⁻¹Ph` is carried by `ȷ` onto the line group of the cusp `ȷ(h)⁻¹ Q ȷ(h)`. -/
theorem jmath_mem_gammaNQAt_iff {N : ℕ} {h A : SL(3, ℤ)} :
    jmath A ∈ gammaNQAt N (jmath h) ↔ A ∈ gammaNPAt N h := by
  rw [mem_gammaNQAt, mem_gammaNPAt, ← jmath_inv, ← jmath_mul, ← jmath_mul, jmath_mem_gammaNQ_iff]

theorem jmath_mem_gammaNPAt_iff {N : ℕ} {h A : SL(3, ℤ)} :
    jmath A ∈ gammaNPAt N (jmath h) ↔ A ∈ gammaNQAt N h := by
  rw [mem_gammaNQAt, mem_gammaNPAt, ← jmath_inv, ← jmath_mul, ← jmath_mul, jmath_mem_gammaNP_iff]

theorem jmath_mem_gammaNBAt_iff {N : ℕ} {h A : SL(3, ℤ)} :
    jmath A ∈ gammaNBAt N (jmath h) ↔ A ∈ gammaNBAt N h := by
  rw [mem_gammaNBAt, mem_gammaNBAt, ← jmath_inv, ← jmath_mul, ← jmath_mul, jmath_mem_gammaNB_iff]

end TernaryPeriodPolynomials.Argument.EisensteinDual
