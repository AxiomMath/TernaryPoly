module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.L1
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Kostant
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CocycleBridge

@[expose] public section


/-!
# The local value at the good line as a parabolic cup product

The Levi factor `GL₂(ℤ)` of the stabilizer of the good line `L₁` contains `S = [[0, -1], [1, 0]]`
(of order four) and `T₀ = [[1, 1], [0, 1]]`; the cone point `S T₀⁻¹ = [[0, -1], [1, -1]]` has order
three, and `T₀ = (S T₀⁻¹)⁻¹ S`. These are the three special elements `S`, `T₀⁻¹`, `(S T₀⁻¹)⁻¹` of
the three-punctured sphere `SL₂(ℤ)\ℍ` used by the parabolic cup pairing of `GL₂(ℤ)`, with the cusp
at `T₀⁻¹`.

Decomposing the fiber defect along `T₀ = (S T₀⁻¹)⁻¹ S` gives the local value at `L₁` in this
presentation (`lineValue_goodLine_cone`), and it is minus the cup formula of `CocycleBridge`
(`lineValue_goodLine_cupFormula`):

  `lineValue = −cupFormula κ (·) S T₀⁻¹ α β (v_S, −(ω − ω_U), v_E)`,

for the crossed homomorphisms `α(g) = g · ω_U − ω_U`, `β(g) = g · θ_U − θ_U` of the left action
`g · f = g⁻¹ ⋆ f` on one-cochains, the Kostant pairing `κ` as coefficient pairing, the cusp
primitive `−(ω − ω_U)` at `T₀⁻¹`, and the torsion primitives `v_S = −¼ Σ_{j<4} A(S^j)` and
`v_E = −⅓ Σ_{j<3} A((S T₀⁻¹)^{-j})`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.FiberLevelOne

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.TopVanishing (IsTopVanishing)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal
open TernaryPeriodPolynomials.BoundaryDuality.ChiHom
open TernaryPeriodPolynomials.BoundaryDuality.CocycleBridge (cupFormula)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
  (prismData latL1 latL1_le isLevi_T₀_L₁ isLevi_U₆_L₁)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
  (S T₀ U₆ L₁ zS zT₀ zc zS_val zc_val zc_mul_self embedZ mkInt U₆_eq
    T₀_mem_levelStabilizer_e₂)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1

/-- Entrywise verification of an identity between explicit `3 × 3` matrices. -/
local macro "matrix_entries" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]))

section Matrices

theorem zT₀_inv_val : (zT₀⁻¹).val = !![1, -1, 0; 0, 1, 0; 0, 0, 1] := rfl

/-- The cone point `S T₀⁻¹ = [[0, -1], [1, -1]]` on the coordinates `(0, 1)`. -/
def zcone : IntegralGL3 :=
  mkInt !![0, -1, 0; 1, -1, 0; 0, 0, 1] !![-1, 1, 0; -1, 0, 0; 0, 0, 1]
    (by matrix_entries) (by matrix_entries)

theorem zcone_val : zcone.val = !![0, -1, 0; 1, -1, 0; 0, 0, 1] := rfl

theorem zcone_eq : zcone = zS * zT₀⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul, zcone_val, zS_val, zT₀_inv_val]
  matrix_entries

theorem zcone_mul_mul : zcone * zcone * zcone = 1 := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_one, zcone_val]
  matrix_entries

theorem zS_mul_self : zS * zS = zc := by
  apply Units.ext
  simp only [Units.val_mul, zS_val, zc_val]
  matrix_entries

theorem zS_pow_four : zS ^ 4 = 1 := by
  have h2 : zS ^ 2 = zc := by
    rw [sq]
    exact zS_mul_self
  calc zS ^ 4 = (zS ^ 2) ^ 2 := pow_mul zS 2 2
    _ = 1 := by
      rw [h2, sq]
      exact zc_mul_self

/-- `S⁴ = 1`. -/
theorem S_pow_four : S ^ 4 = 1 :=
  (map_pow embedZ zS 4).symm.trans ((congrArg embedZ zS_pow_four).trans (map_one embedZ))

/-- The cone point has order three. -/
theorem cone_pow_three : (S * T₀⁻¹) ^ 3 = 1 := by
  have h : S * T₀⁻¹ = embedZ zcone := by
    rw [zcone_eq, map_mul, map_inv]
    rfl
  rw [h, ← map_pow, pow_three', zcone_mul_mul, map_one]

theorem cone_inv_pow_three : (S * T₀⁻¹)⁻¹ ^ 3 = 1 := by
  rw [inv_pow, cone_pow_three, inv_one]

/-- `T₀ = (S T₀⁻¹)⁻¹ S`. -/
theorem T₀_eq_cone : T₀ = (S * T₀⁻¹)⁻¹ * S := by group

theorem S_eq : S = U₆ * T₀⁻¹ := eq_mul_inv_of_mul_eq U₆_eq.symm

end Matrices

section Levi

theorem isLevi_S : IsLevi (levelStabilizer L₁) latL1.sub latL1.σ S := by
  rw [S_eq]
  exact isLevi_U₆_L₁.mul isLevi_T₀_inv

theorem isLevi_S_inv : IsLevi (levelStabilizer L₁) latL1.sub latL1.σ S⁻¹ := by
  rw [S_eq, mul_inv_rev, inv_inv]
  exact isLevi_T₀_L₁.mul isLevi_U₆_inv

theorem isLevi_S_inv_inv : IsLevi (levelStabilizer L₁) latL1.sub latL1.σ S⁻¹⁻¹ := by
  rw [inv_inv]
  exact isLevi_S

theorem isLevi_cone : IsLevi (levelStabilizer L₁) latL1.sub latL1.σ (S * T₀⁻¹) :=
  isLevi_S.mul isLevi_T₀_inv

theorem isLevi_cone_inv : IsLevi (levelStabilizer L₁) latL1.sub latL1.σ (S * T₀⁻¹)⁻¹ := by
  rw [mul_inv_rev, inv_inv]
  exact isLevi_T₀_L₁.mul isLevi_S_inv

theorem isLevi_cone_inv_inv :
    IsLevi (levelStabilizer L₁) latL1.sub latL1.σ (S * T₀⁻¹)⁻¹⁻¹ := by
  rw [inv_inv]
  exact isLevi_cone

theorem isLevi_pow_inv {f : RationalGL3} (hf : IsLevi (levelStabilizer L₁) latL1.sub latL1.σ f⁻¹)
    (j : ℕ) : IsLevi (levelStabilizer L₁) latL1.sub latL1.σ (f ^ j)⁻¹ := by
  rw [← inv_pow]
  exact hf.pow j

end Levi

variable {n : ℕ} {χ : RankOneCharacter}

/-- **The local value at the good line in the presentation `(S, T₀⁻¹)`.** -/
theorem lineValue_goodLine_cone (T : DualityData n χ) (z : MaximalCycles n χ .line)
    (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane) (hw : EdgePrimitive z w)
    (stab : IsTopVanishing (levelStabilizer L₁))
    (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL1.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n χ γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₁)
    (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hθU : ∀ γ ∈ latL1.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n χ (T.φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![T.φ a, T.φ b, T.φ c] (T.dualFlag L₁)) :
    lineValue traceDataL2 T 1 z w y =
      -kostant T.B latL1.σ (pull1 (rationalCoefficientComponent n χ) T₀ (edgeCochain w - ωU))
          (leviCocycle (dualRep T) θU T₀) -
        kostant T.B latL1.σ (pull1 (rationalCoefficientComponent n χ) S
          (leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹))
          (leviCocycle (dualRep T) θU S) +
        (1 / 3 : ℂ) * ∑ j ∈ Finset.range 3, kostant T.B latL1.σ
          (pull1 (rationalCoefficientComponent n χ) (S * T₀⁻¹)⁻¹
            (leviCocycle (rationalCoefficientComponent n χ) ωU ((S * T₀⁻¹)⁻¹ ^ j)))
          (leviCocycle (dualRep T) θU (S * T₀⁻¹)⁻¹) +
        (1 / 4 : ℂ) * ∑ j ∈ Finset.range 4, kostant T.B latL1.σ
          (pull1 (rationalCoefficientComponent n χ) S
            (leviCocycle (rationalCoefficientComponent n χ) ωU (S ^ j)))
          (leviCocycle (dualRep T) θU S) := by
  have hF := fiberHyp_goodLine T z w y hw ωU hωU hdωU θU hθU hdθU
  obtain ⟨K, ν, hP, hval⟩ := lineValue_eq_defect T z w y hw stab ωU hωU hdωU θU hθU hdθU
  rw [hval]
  have hT : defectValue (rationalCoefficientComponent n χ) T.B latL1.σ ωU θU ν T₀ =
      defectValue (rationalCoefficientComponent n χ) T.B latL1.σ ωU θU ν (S * T₀⁻¹)⁻¹ +
        defectValue (rationalCoefficientComponent n χ) T.B latL1.σ ωU θU ν S +
        kostant T.B latL1.σ (pull1 (rationalCoefficientComponent n χ) S
          (leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹))
          (leviCocycle (dualRep T) θU S) := by
    have h := defectValue_mul hF hP (prismData RationalGL3) latL1.boundary_σ isLevi_cone_inv_inv
      isLevi_S_inv
    rw [← T₀_eq_cone] at h
    exact h
  have h3 := defectValue_torsion hF hP (prismData RationalGL3) latL1.boundary_σ
    isLevi_cone_inv_inv cone_inv_pow_three
  have h4 := defectValue_torsion hF hP (prismData RationalGL3) latL1.boundary_σ isLevi_S_inv
    S_pow_four
  push_cast at h3 h4
  linear_combination -hT - (1 / 3 : ℂ) * h3 - (1 / 4 : ℂ) * h4

/-- **The local value at the good line is minus the parabolic cup formula** of the crossed
homomorphisms `α(g) = g · ω_U − ω_U`, `β(g) = g · θ_U − θ_U` (for the left action on one-cochains)
at the special elements `S`, `T₀⁻¹`, `(S T₀⁻¹)⁻¹`, with the Kostant pairing as coefficient pairing
and the primitives `−¼ Σ_{j<4} A(S^j)`, `−(ω − ω_U)`, `−⅓ Σ_{j<3} A((S T₀⁻¹)^{-j})`. -/
theorem lineValue_goodLine_cupFormula (T : DualityData n χ) (z : MaximalCycles n χ .line)
    (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane) (hw : EdgePrimitive z w)
    (stab : IsTopVanishing (levelStabilizer L₁))
    (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL1.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n χ γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₁)
    (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hθU : ∀ γ ∈ latL1.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n χ (T.φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![T.φ a, T.φ b, T.φ c] (T.dualFlag L₁)) :
    lineValue traceDataL2 T 1 z w y =
      -cupFormula (kostantForm T.B latL1.σ) (cochainRep (dualRep T)) S T₀⁻¹
        (fun g => leviCocycle (rationalCoefficientComponent n χ) ωU g⁻¹)
        (fun g => leviCocycle (dualRep T) θU g⁻¹)
        (-(1 / 4 : ℂ) • ∑ j ∈ Finset.range 4,
            leviCocycle (rationalCoefficientComponent n χ) ωU (S ^ j),
          -(edgeCochain w - ωU),
          -(1 / 3 : ℂ) • ∑ j ∈ Finset.range 3,
            leviCocycle (rationalCoefficientComponent n χ) ωU ((S * T₀⁻¹)⁻¹ ^ j)) := by
  have hF := fiberHyp_goodLine T z w y hw ωU hωU hdωU θU hθU hdθU
  have hB := hF.invariant
  have hUΛ := hF.le
  have hσ := latL1.boundary_σ
  rw [lineValue_goodLine_cone T z w y hw stab ωU hωU hdωU θU hθU hdθU]
  -- the unfolded cup formula
  have e : cupFormula (kostantForm T.B latL1.σ) (cochainRep (dualRep T)) S T₀⁻¹
        (fun g => leviCocycle (rationalCoefficientComponent n χ) ωU g⁻¹)
        (fun g => leviCocycle (dualRep T) θU g⁻¹)
        (-(1 / 4 : ℂ) • ∑ j ∈ Finset.range 4,
            leviCocycle (rationalCoefficientComponent n χ) ωU (S ^ j),
          -(edgeCochain w - ωU),
          -(1 / 3 : ℂ) • ∑ j ∈ Finset.range 3,
            leviCocycle (rationalCoefficientComponent n χ) ωU ((S * T₀⁻¹)⁻¹ ^ j)) =
      kostant T.B latL1.σ (leviCocycle (rationalCoefficientComponent n χ) ωU S⁻¹)
          (pull1 (dualRep T) S⁻¹ (leviCocycle (dualRep T) θU T₀)) +
        kostant T.B latL1.σ (leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹)
          (pull1 (dualRep T) (S * T₀⁻¹)⁻¹ (leviCocycle (dualRep T) θU (S * T₀⁻¹))) -
        (kostant T.B latL1.σ (-(1 / 4 : ℂ) • ∑ j ∈ Finset.range 4,
              leviCocycle (rationalCoefficientComponent n χ) ωU (S ^ j))
            (leviCocycle (dualRep T) θU S⁻¹) +
          kostant T.B latL1.σ (-(edgeCochain w - ωU)) (leviCocycle (dualRep T) θU T₀) +
          kostant T.B latL1.σ (-(1 / 3 : ℂ) • ∑ j ∈ Finset.range 3,
              leviCocycle (rationalCoefficientComponent n χ) ωU ((S * T₀⁻¹)⁻¹ ^ j))
            (leviCocycle (dualRep T) θU (S * T₀⁻¹))) := by
    simp only [cupFormula, kostantForm_apply, cochainRep_apply, inv_inv]
  -- the cocycle facts
  have hAS := (uCocycle_leviCocycle hF isLevi_S_inv).1
  have hA'S := (uCocycle_leviCocycle hF isLevi_S_inv).2
  have hA'T₀ := (uCocycle_leviCocycle hF isLevi_T₀_inv).2
  have hAg := (uCocycle_leviCocycle hF isLevi_cone_inv_inv).1
  have hA'g := (uCocycle_leviCocycle hF isLevi_cone_inv_inv).2
  -- the terms of the cup formula
  have F1 : kostant T.B latL1.σ (leviCocycle (rationalCoefficientComponent n χ) ωU S⁻¹)
        (pull1 (dualRep T) S⁻¹ (leviCocycle (dualRep T) θU T₀)) =
      -kostant T.B latL1.σ (leviCocycle (rationalCoefficientComponent n χ) ωU S)
        (leviCocycle (dualRep T) θU T₀) := by
    rw [leviCocycle_inv (rationalCoefficientComponent n χ) ωU S, kostant_neg_left,
      kostant_pull1 (prismData RationalGL3) hσ hB hUΛ isLevi_S_inv_inv hAS hA'T₀]
  have F2 : kostant T.B latL1.σ (leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹)
        (pull1 (dualRep T) (S * T₀⁻¹)⁻¹ (leviCocycle (dualRep T) θU (S * T₀⁻¹))) =
      -kostant T.B latL1.σ (leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹)
        (leviCocycle (dualRep T) θU (S * T₀⁻¹)⁻¹) := by
    rw [leviCocycle_eq_neg_pull1_inv (dualRep T) θU (S * T₀⁻¹), pull1_neg, pull1_mul,
      mul_inv_cancel, pull1_one, kostant_neg_right]
  have F3 : kostant T.B latL1.σ (-(1 / 4 : ℂ) • ∑ j ∈ Finset.range 4,
          leviCocycle (rationalCoefficientComponent n χ) ωU (S ^ j))
        (leviCocycle (dualRep T) θU S⁻¹) =
      (1 / 4 : ℂ) * ∑ j ∈ Finset.range 4, kostant T.B latL1.σ
        (pull1 (rationalCoefficientComponent n χ) S
          (leviCocycle (rationalCoefficientComponent n χ) ωU (S ^ j)))
        (leviCocycle (dualRep T) θU S) := by
    have hsum : ∑ j ∈ Finset.range 4, kostant T.B latL1.σ
          (leviCocycle (rationalCoefficientComponent n χ) ωU (S ^ j))
          (pull1 (dualRep T) S⁻¹ (leviCocycle (dualRep T) θU S)) =
        ∑ j ∈ Finset.range 4, kostant T.B latL1.σ
          (pull1 (rationalCoefficientComponent n χ) S
            (leviCocycle (rationalCoefficientComponent n χ) ωU (S ^ j)))
          (leviCocycle (dualRep T) θU S) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [kostant_shift (prismData RationalGL3) hσ hB hUΛ isLevi_S_inv isLevi_S_inv_inv
        (uCocycle_leviCocycle hF (isLevi_pow_inv isLevi_S_inv j)).1 hA'S, inv_inv]
    rw [leviCocycle_inv (dualRep T) θU S, kostant_neg_right, kostant_smul_left,
      kostant_sum_left, hsum]
    ring
  have F4 : kostant T.B latL1.σ (-(edgeCochain w - ωU)) (leviCocycle (dualRep T) θU T₀) =
      -kostant T.B latL1.σ (edgeCochain w - ωU) (leviCocycle (dualRep T) θU T₀) :=
    kostant_neg_left _ _ _ _
  have F5 : kostant T.B latL1.σ (-(1 / 3 : ℂ) • ∑ j ∈ Finset.range 3,
          leviCocycle (rationalCoefficientComponent n χ) ωU ((S * T₀⁻¹)⁻¹ ^ j))
        (leviCocycle (dualRep T) θU (S * T₀⁻¹)) =
      (1 / 3 : ℂ) * ∑ j ∈ Finset.range 3, kostant T.B latL1.σ
        (pull1 (rationalCoefficientComponent n χ) (S * T₀⁻¹)⁻¹
          (leviCocycle (rationalCoefficientComponent n χ) ωU ((S * T₀⁻¹)⁻¹ ^ j)))
        (leviCocycle (dualRep T) θU (S * T₀⁻¹)⁻¹) := by
    have hsum : ∑ j ∈ Finset.range 3, kostant T.B latL1.σ
          (leviCocycle (rationalCoefficientComponent n χ) ωU ((S * T₀⁻¹)⁻¹ ^ j))
          (pull1 (dualRep T) (S * T₀⁻¹) (leviCocycle (dualRep T) θU (S * T₀⁻¹)⁻¹)) =
        ∑ j ∈ Finset.range 3, kostant T.B latL1.σ
          (pull1 (rationalCoefficientComponent n χ) (S * T₀⁻¹)⁻¹
            (leviCocycle (rationalCoefficientComponent n χ) ωU ((S * T₀⁻¹)⁻¹ ^ j)))
          (leviCocycle (dualRep T) θU (S * T₀⁻¹)⁻¹) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [kostant_shift (prismData RationalGL3) hσ hB hUΛ isLevi_cone isLevi_cone_inv
        (uCocycle_leviCocycle hF (isLevi_pow_inv isLevi_cone_inv_inv j)).1 hA'g]
    rw [leviCocycle_eq_neg_pull1_inv (dualRep T) θU (S * T₀⁻¹), kostant_neg_right,
      kostant_smul_left, kostant_sum_left, hsum]
    ring
  have F6 : kostant T.B latL1.σ
        (pull1 (rationalCoefficientComponent n χ) T₀ (edgeCochain w - ωU))
        (leviCocycle (dualRep T) θU T₀) =
      kostant T.B latL1.σ (edgeCochain w - ωU) (leviCocycle (dualRep T) θU T₀) -
        kostant T.B latL1.σ (leviCocycle (rationalCoefficientComponent n χ) ωU T₀)
          (leviCocycle (dualRep T) θU T₀) := by
    rw [pull1_cusp hF T₀_mem_levelStabilizer_e₂, kostant_sub_left]
  have hA : leviCocycle (rationalCoefficientComponent n χ) ωU T₀ =
      leviCocycle (rationalCoefficientComponent n χ) ωU S +
        pull1 (rationalCoefficientComponent n χ) S
          (leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹) := by
    have h := leviCocycle_mul (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹ S
    rw [← T₀_eq_cone] at h
    exact h
  have hA' : leviCocycle (dualRep T) θU T₀ =
      leviCocycle (dualRep T) θU S +
        pull1 (dualRep T) S (leviCocycle (dualRep T) θU (S * T₀⁻¹)⁻¹) := by
    have h := leviCocycle_mul (dualRep T) θU (S * T₀⁻¹)⁻¹ S
    rw [← T₀_eq_cone] at h
    exact h
  have F7 : kostant T.B latL1.σ (leviCocycle (rationalCoefficientComponent n χ) ωU T₀)
        (leviCocycle (dualRep T) θU T₀) =
      kostant T.B latL1.σ (leviCocycle (rationalCoefficientComponent n χ) ωU S)
          (leviCocycle (dualRep T) θU T₀) +
        kostant T.B latL1.σ (pull1 (rationalCoefficientComponent n χ) S
          (leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹))
          (leviCocycle (dualRep T) θU S) +
        kostant T.B latL1.σ (leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹)
          (leviCocycle (dualRep T) θU (S * T₀⁻¹)⁻¹) := by
    have h1 : kostant T.B latL1.σ (pull1 (rationalCoefficientComponent n χ) S
          (leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹))
          (leviCocycle (dualRep T) θU T₀) =
        kostant T.B latL1.σ (pull1 (rationalCoefficientComponent n χ) S
          (leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹))
          (leviCocycle (dualRep T) θU S) +
        kostant T.B latL1.σ (leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹)
          (leviCocycle (dualRep T) θU (S * T₀⁻¹)⁻¹) := by
      rw [hA', kostant_add_right,
        kostant_pull1 (prismData RationalGL3) hσ hB hUΛ isLevi_S_inv hAg hA'g]
    rw [hA, kostant_add_left, h1]
    ring
  linear_combination e + F1 + F2 - F3 - F4 - F5 - F6 + F7

end TernaryPeriodPolynomials.BoundaryDuality.FiberLevelOne
