module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Formula
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Fill
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Trace

@[expose] public section


/-!
# Fiber integration of the local value at the good line cusp

The good line `L₁ = ⟨e₃⟩` has stabilizer `U ⋊ GL₂(ℤ)` in the level, with lattice
`U = {I + 3x E₂₀ + 3y E₂₁}` and torus cycle `σ`, and one orbit of complete flags above it,
represented by `e₂` with the cusp cycle `C(T₀)`, `T₀ = I + E₀₁`. The Levi relation is
`T₀ = U₆ g₄` with `U₆⁶ = g₄⁴ = 1`.

Let `z` be a line two-cocycle with edge primitive `w` and `y` a plane two-cocycle, for any rank
one character `χ`. Write `ζ = z(·)(L₁)`, `ω = w(·)(e₂)` and `η = y(φ ·)(F)` at the dual plane
`F` of `L₁`, `ρ` for the coefficients and `ρ' = ρ ∘ φ`. Suppose that the restrictions of `ζ` and
`η` to `U` are exact, `ζ = dω_U` and `η = dθ_U` with `U`-equivariant `ω_U`, `θ_U` (the local
classes lie in the part `E^{1,1}` of the Hochschild–Serre filtration), and that `H⁴` of the
stabilizer of `L₁` vanishes. With the Levi cocycles `A(h) = h ⋆ ω_U − ω_U`,
`A'(h) = h ⋆ θ_U − θ_U` and the Kostant pairing `κ(f, g) = ⟨f ⌣ g, σ⟩`, the local value of the
boundary trace at `L₁` is (`lineValue_goodLine`)

  `−κ(T₀ ⋆ (ω − ω_U), A'(T₀)) − κ(g₄ ⋆ A(U₆), A'(g₄))
     + ⅙ Σ_{j<6} κ(U₆ ⋆ A(U₆^j), A'(U₆)) + ¼ Σ_{j<4} κ(g₄ ⋆ A(g₄^j), A'(g₄))`.

The filling chain of the trace is replaced by a primitive of `ζ ⌣ η` (`FiberFill`), the
correction of the cusp cycle by a `U`-primitive (`FiberCusp`), and the remaining defect is
computed from the torsion relations (`FiberFormula`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.FiberL1

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.TopVanishing (IsTopVanishing)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal
open TernaryPeriodPolynomials.BoundaryDuality.ChiHom
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
  (prismData latL1 latL1_le latL1_le_e₂ isLevi_T₀_L₁ isLevi_U₆_L₁ isLevi_g₄_L₁ cycleT₀L)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
  (T₀ U₆ g₄ L₁ e₂ T₀_eq U₆_pow_six g₄_pow_four T₀_mem_levelStabilizer_e₂ endpoint_line_e₂)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula
open TernaryPeriodPolynomials.BoundaryDuality.FiberFill

variable {n : ℕ} {χ : RankOneCharacter}

section Levi

theorem g₄_inv : g₄⁻¹ = g₄ ^ 3 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact g₄_pow_four)

theorem U₆_inv : U₆⁻¹ = U₆ ^ 5 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact U₆_pow_six)

theorem isLevi_U₆_inv : IsLevi (levelStabilizer L₁) latL1.sub latL1.σ U₆⁻¹ := by
  rw [U₆_inv]
  exact isLevi_U₆_L₁.pow 5

theorem isLevi_g₄_inv : IsLevi (levelStabilizer L₁) latL1.sub latL1.σ g₄⁻¹ := by
  rw [g₄_inv]
  exact isLevi_g₄_L₁.pow 3

theorem isLevi_T₀_inv : IsLevi (levelStabilizer L₁) latL1.sub latL1.σ T₀⁻¹ := by
  rw [T₀_eq, mul_inv_rev]
  exact isLevi_g₄_inv.mul isLevi_U₆_inv

end Levi

section Local

/-- The coefficients of the dual plane class: `ρ ∘ φ`. -/
def dualRep (T : DualityData n χ) : Representation ℂ RationalGL3 (HomogeneousPoly n) :=
  (rationalCoefficientComponent n χ).comp T.φ

/-- The line cocycle at the good line `L₁`. -/
def lineCocycle (z : MaximalCycles n χ .line) : (Fin 3 → RationalGL3) → HomogeneousPoly n :=
  fun x => z.val.val x L₁

/-- The plane cocycle at the dual plane of `L₁`, with vertices moved by `φ`. -/
def planeCocycle (T : DualityData n χ) (y : MaximalCycles n χ .plane) :
    (Fin 3 → RationalGL3) → HomogeneousPoly n :=
  fun x => y.val.val ![T.φ (x 0), T.φ (x 1), T.φ (x 2)] (T.dualFlag L₁)

/-- The edge primitive at the complete flag `e₂` above `L₁`. -/
def edgeCochain (w : EdgeCochains n χ 1) : (Fin 2 → RationalGL3) → HomogeneousPoly n :=
  fun x => w.val x e₂

/-- The hypotheses of the fiber integration at the good line. -/
theorem fiberHyp_goodLine (T : DualityData n χ) (z : MaximalCycles n χ .line)
    (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane) (hw : EdgePrimitive z w)
    (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL1.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n χ γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₁)
    (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hθU : ∀ γ ∈ latL1.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n χ (T.φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![T.φ a, T.φ b, T.φ c] (T.dualFlag L₁)) :
    FiberHyp (rationalCoefficientComponent n χ) (dualRep T) T.B (levelStabilizer L₁)
      (levelStabilizer e₂) latL1.sub (lineCocycle z) (planeCocycle T y) (edgeCochain w) ωU
      θU :=
  { le := latL1_le
    le_edge := latL1_le_e₂
    invariant := fun g hg v v' => T.invariant g (Subgroup.mem_inf.mp hg).1 v v'
    zeta_eq := fun γ hγ a b c => by
      have level : γ ∈ rationalLevel := (Subgroup.mem_inf.mp hγ).1
      have fixed : γ • L₁ = L₁ := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hγ).2
      have h := congrFun (cochain_triple z.val ⟨γ, level⟩ a b c) L₁
      change z.val.val ![γ * a, γ * b, γ * c] L₁ =
        rationalCoefficientComponent n χ γ (z.val.val ![a, b, c] (γ⁻¹ • L₁)) at h
      rw [inv_smul_eq_iff.mpr fixed.symm] at h
      exact h
    zeta_cocycle := fun x => congrFun (isCocycleTwo_of_mem z x) L₁
    eta_eq := fun γ hγ a b c => by
      have level : γ ∈ rationalLevel := (Subgroup.mem_inf.mp hγ).1
      have fixed : γ • L₁ = L₁ := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hγ).2
      have dual : T.φ γ ∈ rationalLevel := T.level γ level
      have fixedF : (T.φ γ)⁻¹ • T.dualFlag L₁ = T.dualFlag L₁ := by
        rw [inv_smul_eq_iff, ← T.dualFlag_smul, fixed]
      have h := congrFun (cochain_triple y.val ⟨T.φ γ, dual⟩ (T.φ a) (T.φ b) (T.φ c))
        (T.dualFlag L₁)
      change y.val.val ![T.φ γ * T.φ a, T.φ γ * T.φ b, T.φ γ * T.φ c] (T.dualFlag L₁) =
        rationalCoefficientComponent n χ (T.φ γ)
          (y.val.val ![T.φ a, T.φ b, T.φ c] ((T.φ γ)⁻¹ • T.dualFlag L₁)) at h
      rw [fixedF] at h
      change y.val.val ![T.φ (γ * a), T.φ (γ * b), T.φ (γ * c)] (T.dualFlag L₁) =
        rationalCoefficientComponent n χ (T.φ γ)
          (y.val.val ![T.φ a, T.φ b, T.φ c] (T.dualFlag L₁))
      rw [map_mul, map_mul, map_mul]
      exact h
    eta_cocycle := fun x =>
      congrFun (isCocycleTwo_of_mem y ![T.φ (x 0), T.φ (x 1), T.φ (x 2), T.φ (x 3)])
        (T.dualFlag L₁)
    omega_eq := fun γ hγ a b => by
      have level : γ ∈ rationalLevel := (Subgroup.mem_inf.mp hγ).1
      have fixed : γ • e₂ = e₂ := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hγ).2
      have h := congrFun (cochain_pair w ⟨γ, level⟩ a b) e₂
      change w.val ![γ * a, γ * b] e₂ =
        rationalCoefficientComponent n χ γ (w.val ![a, b] (γ⁻¹ • e₂)) at h
      rw [inv_smul_eq_iff.mpr fixed.symm] at h
      exact h
    omega_d := fun a b c => by
      have h := hw ![a, b, c] e₂
      rw [endpoint_line_e₂] at h
      exact h.symm
    omegaU_eq := hωU
    omegaU_d := hdωU
    thetaU_eq := hθU
    thetaU_d := hdθU }

end Local

section Value

/-- The sums over the edges above the good line have the single term `e₂`. -/
theorem sum_lineOf_one {M : Type} [AddCommMonoid M] (g : Fin 3 → M) :
    ∑ i ∈ Finset.univ.filter (fun i => traceDataL2.lineOf i = 1), g i = g 2 := by
  rw [Finset.sum_filter, Fin.sum_univ_three]
  have h0 : traceDataL2.lineOf 0 = 0 := rfl
  have h1 : traceDataL2.lineOf 1 = 0 := rfl
  have h2 : traceDataL2.lineOf 2 = 1 := rfl
  have h01 : ¬((0 : Fin 2) = 1) := by decide
  rw [h0, h1, h2, ite_eq_right h01, ite_eq_right h01, ite_eq_left (rfl : (1 : Fin 2) = 1), zero_add, zero_add]

/-- The chain of the trace at `e₂` is the cusp cycle `C_{L₁}(T₀)`. -/
theorem chain_two : traceDataL2.chain 2 = cycleT₀L := by
  change ((-1 : ℂ) / (-1)) • cycleT₀L = cycleT₀L
  rw [div_self (by norm_num : (-1 : ℂ) ≠ 0), one_smul]

/-- **The local value at the good line without the filling chain**: for an invariant primitive
`K` of `ζ ⌣ η`, the local value is `⟨ω ⌣ η − K, C(T₀)⟩`. -/
theorem lineValue_one_eq (T : DualityData n χ) (z : MaximalCycles n χ .line)
    (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane) (K : (Fin 4 → RationalGL3) → ℂ)
    (hK : ∀ (γ : levelStabilizer L₁) x, K (fun i => γ.val * x i) = K x)
    (hdK : ∀ x, differentialThreeRaw K x = cup22 T.B (lineCocycle z) (planeCocycle T y) x) :
    lineValue traceDataL2 T 1 z w y =
      Finsupp.linearCombination ℂ (cup12 T.B (edgeCochain w) (planeCocycle T y) - K)
        cycleT₀L := by
  rw [lineValue_eq_of_primitive traceDataL2 T 1 z w y K hK hdK, sum_lineOf_one, sum_lineOf_one,
    pair_sub, chain_two]
  rfl

/-- **The local value at the good line through the fiber defect**: there are primitives `K`, `ν`
for which the local value is `−κ(T₀ ⋆ (ω − ω_U), A'(T₀)) − e(T₀)`. -/
theorem lineValue_eq_defect (T : DualityData n χ) (z : MaximalCycles n χ .line)
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
    ∃ (K : (Fin 4 → RationalGL3) → ℂ) (ν : (Fin 3 → RationalGL3) → ℂ),
      Primitives T.B (levelStabilizer L₁) latL1.sub (lineCocycle z) (planeCocycle T y) ωU K ν ∧
      lineValue traceDataL2 T 1 z w y =
        -kostant T.B latL1.σ (pull1 (rationalCoefficientComponent n χ) T₀ (edgeCochain w - ωU))
            (leviCocycle (dualRep T) θU T₀) -
          defectValue (rationalCoefficientComponent n χ) T.B latL1.σ ωU θU ν T₀ := by
  have hF := fiberHyp_goodLine T z w y hw ωU hωU hdωU θU hθU hdθU
  obtain ⟨K, ν, hP⟩ := exists_primitives hF stab latL1.topVanishingThree
  refine ⟨K, ν, hP, ?_⟩
  rw [lineValue_one_eq T z w y K hP.K_inv hP.K_d,
    show cycleT₀L = cusp (prismData RationalGL3) latL1.σ isLevi_T₀_L₁ from rfl,
    pair_cusp_eq hF hP (prismData RationalGL3) latL1.boundary_σ isLevi_T₀_L₁ isLevi_T₀_inv
      T₀_mem_levelStabilizer_e₂]

/-- **Fiber integration at the good line.** The local value of the boundary trace at `L₁` is the
explicit Levi expression in the Levi cocycles `A`, `A'`, the cusp primitive `ω − ω_U` and the
Kostant pairing. -/
theorem lineValue_goodLine (T : DualityData n χ) (z : MaximalCycles n χ .line)
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
        kostant T.B latL1.σ (pull1 (rationalCoefficientComponent n χ) g₄
          (leviCocycle (rationalCoefficientComponent n χ) ωU U₆))
          (leviCocycle (dualRep T) θU g₄) +
        (1 / 6 : ℂ) * ∑ j ∈ Finset.range 6, kostant T.B latL1.σ
          (pull1 (rationalCoefficientComponent n χ) U₆
            (leviCocycle (rationalCoefficientComponent n χ) ωU (U₆ ^ j)))
          (leviCocycle (dualRep T) θU U₆) +
        (1 / 4 : ℂ) * ∑ j ∈ Finset.range 4, kostant T.B latL1.σ
          (pull1 (rationalCoefficientComponent n χ) g₄
            (leviCocycle (rationalCoefficientComponent n χ) ωU (g₄ ^ j)))
          (leviCocycle (dualRep T) θU g₄) := by
  have hF := fiberHyp_goodLine T z w y hw ωU hωU hdωU θU hθU hdθU
  obtain ⟨K, ν, hP, hval⟩ := lineValue_eq_defect T z w y hw stab ωU hωU hdωU θU hθU hdθU
  rw [hval]
  have hT : defectValue (rationalCoefficientComponent n χ) T.B latL1.σ ωU θU ν T₀ =
      defectValue (rationalCoefficientComponent n χ) T.B latL1.σ ωU θU ν U₆ +
        defectValue (rationalCoefficientComponent n χ) T.B latL1.σ ωU θU ν g₄ +
        kostant T.B latL1.σ (pull1 (rationalCoefficientComponent n χ) g₄
          (leviCocycle (rationalCoefficientComponent n χ) ωU U₆))
          (leviCocycle (dualRep T) θU g₄) := by
    rw [T₀_eq]
    exact defectValue_mul hF hP (prismData RationalGL3) latL1.boundary_σ isLevi_U₆_inv
      isLevi_g₄_inv
  have h6 := defectValue_torsion hF hP (prismData RationalGL3) latL1.boundary_σ isLevi_U₆_inv
    U₆_pow_six
  have h4 := defectValue_torsion hF hP (prismData RationalGL3) latL1.boundary_σ isLevi_g₄_inv
    g₄_pow_four
  push_cast at h6 h4
  linear_combination -hT - (1 / 6 : ℂ) * h6 - (1 / 4 : ℂ) * h4

end Value

end TernaryPeriodPolynomials.BoundaryDuality.FiberL1
