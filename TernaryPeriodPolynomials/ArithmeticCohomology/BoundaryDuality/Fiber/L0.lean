module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.LevelOne

@[expose] public section


/-!
# Fiber integration of the local value at the bad line cusp

The bad line `L₀ = ⟨e₁⟩` has stabilizer `U ⋊ (±1 × Γ₁'(3))` in the level, with lattice
`U = {I + x E₀₁ + y E₀₂}` and torus cycle `σ`, and two orbits of complete flags above it: `e₀`
with the cusp cycle `C(T)`, `T = I + E₁₂`, and `e₁` with `−C(L)`, `L = I + 3E₂₁`. The Levi relation
is `T = t L` for the cone point `t = T L⁻¹` of order three.

For a line two-cocycle `z` with edge primitive `w`, a plane two-cocycle `y`, and `U`-primitives
`ω_U`, `θ_U` of `ζ = z(·)(L₀)` and `η = y(φ ·)(F)` (`F` the dual plane of `L₀`), with
`c₀ = w(·)(e₀) − ω_U` and `c₁ = w(·)(e₁) − ω_U`, the local value of the boundary trace at `L₀` is
(`lineValue_badLine_cupFormula`)

  `lineValue = cupFormula κ (·) T L⁻¹ α β (−c₀, −c₁, −⅓ Σ_{j<3} A(t^{-j}))`,

the cup formula of `CocycleBridge` at the special elements `T`, `L⁻¹`, `(T L⁻¹)⁻¹` of `Γ₁(3)`
(the two cusps and the cone point), with the Kostant pairing `κ` as coefficient pairing.
`lineValue_badLine` gives the same value as an explicit Levi expression.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.FiberL0

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.TopVanishing (IsTopVanishing)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal
open TernaryPeriodPolynomials.BoundaryDuality.ChiHom
open TernaryPeriodPolynomials.BoundaryDuality.CocycleBridge (cupFormula)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
  (prismData latL0 latL0_le latL0_le_e₀ latL0_le_e₁ isLevi_T isLevi_L isLevi_of_conj cycleT
    cycleL)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
  (L E L₀ e₀ e₁ uL0 T_conj_uL0 L_conj_uL0 T_eq E_eq E_pow_three T_mem_levelStabilizer_L₀
    L_mem_levelStabilizer_L₀ T_mem_levelStabilizer_e₀ L_mem_levelStabilizer_e₁ endpoint_line_e₀
    endpoint_line_e₁)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant
open TernaryPeriodPolynomials.BoundaryDuality.FiberFill
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)

/-- The unipotent Levi element `T = I + E₁₂` at the bad line. -/
local notation "Tm" => TernaryPeriodPolynomials.BoundaryDuality.L2Matrices.T

variable {n : ℕ} {χ : RankOneCharacter}

section Levi

theorem T_conj_inv (x y : ℤ) : Tm⁻¹⁻¹ * uL0 x y * Tm⁻¹ = uL0 x (y - x) := by
  have h := T_conj_uL0 x (y - x)
  rw [show x + (y - x) = y by ring] at h
  rw [inv_inv, ← h]
  group

theorem L_conj_inv (x y : ℤ) : L⁻¹⁻¹ * uL0 x y * L⁻¹ = uL0 (x - 3 * y) y := by
  have h := L_conj_uL0 (x - 3 * y) y
  rw [show x - 3 * y + 3 * y = x by ring] at h
  rw [inv_inv, ← h]
  group

theorem isLevi_T_inv : IsLevi (levelStabilizer L₀) latL0.sub latL0.σ Tm⁻¹ :=
  isLevi_of_conj latL0 (Subgroup.inv_mem _ T_mem_levelStabilizer_L₀) (p := 1) (q := -1)
    (r := 0) (s := 1)
    (by show Tm⁻¹⁻¹ * uL0 1 0 * Tm⁻¹ = uL0 1 (-1); rw [T_conj_inv]; norm_num)
    (by show Tm⁻¹⁻¹ * uL0 0 1 * Tm⁻¹ = uL0 0 1; rw [T_conj_inv]; norm_num) (by norm_num)

theorem isLevi_L_inv : IsLevi (levelStabilizer L₀) latL0.sub latL0.σ L⁻¹ :=
  isLevi_of_conj latL0 (Subgroup.inv_mem _ L_mem_levelStabilizer_L₀) (p := 1) (q := 0)
    (r := -3) (s := 1)
    (by show L⁻¹⁻¹ * uL0 1 0 * L⁻¹ = uL0 1 0; rw [L_conj_inv]; norm_num)
    (by show L⁻¹⁻¹ * uL0 0 1 * L⁻¹ = uL0 (-3) 1; rw [L_conj_inv]; norm_num) (by norm_num)

theorem isLevi_T_inv_inv : IsLevi (levelStabilizer L₀) latL0.sub latL0.σ Tm⁻¹⁻¹ := by
  rw [inv_inv]
  exact isLevi_T

theorem isLevi_L_inv_inv : IsLevi (levelStabilizer L₀) latL0.sub latL0.σ L⁻¹⁻¹ := by
  rw [inv_inv]
  exact isLevi_L

theorem isLevi_cone0 : IsLevi (levelStabilizer L₀) latL0.sub latL0.σ (Tm * L⁻¹) :=
  isLevi_T.mul isLevi_L_inv

theorem isLevi_cone0_inv : IsLevi (levelStabilizer L₀) latL0.sub latL0.σ (Tm * L⁻¹)⁻¹ := by
  rw [mul_inv_rev, inv_inv]
  exact isLevi_L.mul isLevi_T_inv

theorem isLevi_cone0_inv_inv :
    IsLevi (levelStabilizer L₀) latL0.sub latL0.σ (Tm * L⁻¹)⁻¹⁻¹ := by
  rw [inv_inv]
  exact isLevi_cone0

theorem isLevi_pow_inv0 {f : RationalGL3}
    (hf : IsLevi (levelStabilizer L₀) latL0.sub latL0.σ f⁻¹) (j : ℕ) :
    IsLevi (levelStabilizer L₀) latL0.sub latL0.σ (f ^ j)⁻¹ := by
  rw [← inv_pow]
  exact hf.pow j

theorem cone0_inv_pow_three : (Tm * L⁻¹)⁻¹ ^ 3 = 1 := by
  rw [inv_pow, ← E_eq, E_pow_three, inv_one]

theorem T_eq_cone0 : Tm = Tm * L⁻¹ * L := by group

end Levi

section Local

/-- **The hypotheses of the fiber integration at a line**, for any line flag `Lf`, complete flag
`e` above it and lattice `U` in their stabilizers. -/
theorem fiberHyp_line (Td : DualityData n χ) {Lf : Flags .line} {e : Edges}
    (he : endpoint .line e = Lf) {U : Subgroup RationalGL3} (hUL : U ≤ levelStabilizer Lf)
    (hUe : U ≤ levelStabilizer e) (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1)
    (y : MaximalCycles n χ .plane) (hw : EdgePrimitive z w)
    (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ U, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n χ γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] Lf)
    (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hθU : ∀ γ ∈ U, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n χ (Td.φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![Td.φ a, Td.φ b, Td.φ c] (Td.dualFlag Lf)) :
    FiberHyp (rationalCoefficientComponent n χ) (dualRep Td) Td.B (levelStabilizer Lf)
      (levelStabilizer e) U (fun x => z.val.val x Lf)
      (fun x => y.val.val ![Td.φ (x 0), Td.φ (x 1), Td.φ (x 2)] (Td.dualFlag Lf))
      (fun x => w.val x e) ωU θU :=
  { le := hUL
    le_edge := hUe
    invariant := fun g hg v v' => Td.invariant g (Subgroup.mem_inf.mp hg).1 v v'
    zeta_eq := fun γ hγ a b c => by
      have level : γ ∈ rationalLevel := (Subgroup.mem_inf.mp hγ).1
      have fixed : γ • Lf = Lf := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hγ).2
      have h := congrFun (cochain_triple z.val ⟨γ, level⟩ a b c) Lf
      change z.val.val ![γ * a, γ * b, γ * c] Lf =
        rationalCoefficientComponent n χ γ (z.val.val ![a, b, c] (γ⁻¹ • Lf)) at h
      rw [inv_smul_eq_iff.mpr fixed.symm] at h
      exact h
    zeta_cocycle := fun x => congrFun (isCocycleTwo_of_mem z x) Lf
    eta_eq := fun γ hγ a b c => by
      have level : γ ∈ rationalLevel := (Subgroup.mem_inf.mp hγ).1
      have fixed : γ • Lf = Lf := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hγ).2
      have dual : Td.φ γ ∈ rationalLevel := Td.level γ level
      have fixedF : (Td.φ γ)⁻¹ • Td.dualFlag Lf = Td.dualFlag Lf := by
        rw [inv_smul_eq_iff, ← Td.dualFlag_smul, fixed]
      have h := congrFun (cochain_triple y.val ⟨Td.φ γ, dual⟩ (Td.φ a) (Td.φ b) (Td.φ c))
        (Td.dualFlag Lf)
      change y.val.val ![Td.φ γ * Td.φ a, Td.φ γ * Td.φ b, Td.φ γ * Td.φ c] (Td.dualFlag Lf) =
        rationalCoefficientComponent n χ (Td.φ γ)
          (y.val.val ![Td.φ a, Td.φ b, Td.φ c] ((Td.φ γ)⁻¹ • Td.dualFlag Lf)) at h
      rw [fixedF] at h
      change y.val.val ![Td.φ (γ * a), Td.φ (γ * b), Td.φ (γ * c)] (Td.dualFlag Lf) =
        rationalCoefficientComponent n χ (Td.φ γ)
          (y.val.val ![Td.φ a, Td.φ b, Td.φ c] (Td.dualFlag Lf))
      rw [map_mul, map_mul, map_mul]
      exact h
    eta_cocycle := fun x =>
      congrFun (isCocycleTwo_of_mem y ![Td.φ (x 0), Td.φ (x 1), Td.φ (x 2), Td.φ (x 3)])
        (Td.dualFlag Lf)
    omega_eq := fun γ hγ a b => by
      have level : γ ∈ rationalLevel := (Subgroup.mem_inf.mp hγ).1
      have fixed : γ • e = e := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hγ).2
      have h := congrFun (cochain_pair w ⟨γ, level⟩ a b) e
      change w.val ![γ * a, γ * b] e =
        rationalCoefficientComponent n χ γ (w.val ![a, b] (γ⁻¹ • e)) at h
      rw [inv_smul_eq_iff.mpr fixed.symm] at h
      exact h
    omega_d := fun a b c => by
      have h := hw ![a, b, c] e
      rw [he] at h
      exact h.symm
    omegaU_eq := hωU
    omegaU_d := hdωU
    thetaU_eq := hθU
    thetaU_d := hdθU }

/-- The local value without the filling chain, with the edge terms written as cup products. -/
theorem lineValue_eq_of_primitive' {ι L' P : Type} [Fintype ι] [Fintype L'] [Fintype P]
    [DecidableEq L'] [DecidableEq P] (Θ : TraceData ι L' P) (Td : DualityData n χ) (v : L')
    (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane)
    (K : (Fin 4 → RationalGL3) → ℂ)
    (hK : ∀ (γ : levelStabilizer (Θ.lineRep v)) x, K (fun i => γ.val * x i) = K x)
    (hdK : ∀ x, differentialThreeRaw K x = Td.B (z.val.val ![x 0, x 1, x 2] (Θ.lineRep v))
      (y.val.val ![Td.φ (x 2), Td.φ (x 3), Td.φ (x 4)] (Td.dualFlag (Θ.lineRep v)))) :
    lineValue Θ Td v z w y =
      (∑ i ∈ Finset.univ.filter (fun i => Θ.lineOf i = v),
        Finsupp.linearCombination ℂ (cup12 Td.B (fun x => w.val x (Θ.edge i))
          (fun x => y.val.val ![Td.φ (x 0), Td.φ (x 1), Td.φ (x 2)]
            (Td.dualFlag (Θ.lineRep v)))) (Θ.chain i)) -
      Finsupp.linearCombination ℂ K
        (∑ i ∈ Finset.univ.filter (fun i => Θ.lineOf i = v), Θ.chain i) :=
  lineValue_eq_of_primitive Θ Td v z w y K hK hdK

/-- The sums over the edges above the bad line have the two terms `e₀`, `e₁`. -/
theorem sum_lineOf_zero {M : Type} [AddCommMonoid M] (g : Fin 3 → M) :
    ∑ i ∈ Finset.univ.filter (fun i => traceDataL2.lineOf i = 0), g i = g 0 + g 1 := by
  rw [Finset.sum_filter, Fin.sum_univ_three]
  have h0 : traceDataL2.lineOf 0 = 0 := rfl
  have h1 : traceDataL2.lineOf 1 = 0 := rfl
  have h2 : traceDataL2.lineOf 2 = 1 := rfl
  have h10 : ¬((1 : Fin 2) = 0) := by decide
  rw [h0, h1, h2, ite_eq_left (rfl : (0 : Fin 2) = 0), ite_eq_left (rfl : (0 : Fin 2) = 0), ite_eq_right h10,
    add_zero]

/-- **The local value at the bad line without the filling chain.** -/
theorem lineValue_zero_eq (Td : DualityData n χ) (z : MaximalCycles n χ .line)
    (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane) (K : (Fin 4 → RationalGL3) → ℂ)
    (hK : ∀ (γ : levelStabilizer L₀) x, K (fun i => γ.val * x i) = K x)
    (hdK : ∀ x, differentialThreeRaw K x = cup22 Td.B (fun x => z.val.val x L₀)
      (fun x => y.val.val ![Td.φ (x 0), Td.φ (x 1), Td.φ (x 2)] (Td.dualFlag L₀)) x) :
    lineValue traceDataL2 Td 0 z w y =
      Finsupp.linearCombination ℂ (cup12 Td.B (fun x => w.val x e₀)
          (fun x => y.val.val ![Td.φ (x 0), Td.φ (x 1), Td.φ (x 2)] (Td.dualFlag L₀)) - K)
          cycleT -
        Finsupp.linearCombination ℂ (cup12 Td.B (fun x => w.val x e₁)
          (fun x => y.val.val ![Td.φ (x 0), Td.φ (x 1), Td.φ (x 2)] (Td.dualFlag L₀)) - K)
          cycleL := by
  rw [lineValue_eq_of_primitive' traceDataL2 Td 0 z w y K hK hdK, sum_lineOf_zero,
    sum_lineOf_zero, show traceDataL2.edge 0 = e₀ from rfl, show traceDataL2.edge 1 = e₁ from rfl,
    show traceDataL2.lineRep 0 = L₀ from rfl, show traceDataL2.chain 0 = cycleT from rfl,
    show traceDataL2.chain 1 = -cycleL from rfl, map_add, map_neg, map_neg, pair_sub, pair_sub]
  ring

end Local

section Value

/-- **Fiber integration at the bad line**, as an explicit Levi expression in the Levi cocycles
`A`, `A'`, the two cusp primitives and the Kostant pairing (`t = T L⁻¹`). -/
theorem lineValue_badLine (Td : DualityData n χ) (z : MaximalCycles n χ .line)
    (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane) (hw : EdgePrimitive z w)
    (stab : IsTopVanishing (levelStabilizer L₀))
    (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL0.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n χ γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀)
    (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hθU : ∀ γ ∈ latL0.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n χ (Td.φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![Td.φ a, Td.φ b, Td.φ c] (Td.dualFlag L₀)) :
    lineValue traceDataL2 Td 0 z w y =
      -kostant Td.B latL0.σ (pull1 (rationalCoefficientComponent n χ) Tm
          ((fun x => w.val x e₀) - ωU)) (leviCocycle (dualRep Td) θU Tm) +
        kostant Td.B latL0.σ (pull1 (rationalCoefficientComponent n χ) L
          ((fun x => w.val x e₁) - ωU)) (leviCocycle (dualRep Td) θU L) -
        kostant Td.B latL0.σ (pull1 (rationalCoefficientComponent n χ) L
          (leviCocycle (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹)))
          (leviCocycle (dualRep Td) θU L) +
        kostant Td.B latL0.σ (pull1 (rationalCoefficientComponent n χ) (Tm * L⁻¹)
          (leviCocycle (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹)⁻¹))
          (leviCocycle (dualRep Td) θU (Tm * L⁻¹)) -
        (1 / 3 : ℂ) * ∑ j ∈ Finset.range 3, kostant Td.B latL0.σ
          (pull1 (rationalCoefficientComponent n χ) (Tm * L⁻¹)⁻¹
            (leviCocycle (rationalCoefficientComponent n χ) ωU ((Tm * L⁻¹)⁻¹ ^ j)))
          (leviCocycle (dualRep Td) θU (Tm * L⁻¹)⁻¹) := by
  have hF₀ := fiberHyp_line Td endpoint_line_e₀ latL0_le latL0_le_e₀ z w y hw ωU hωU hdωU θU hθU
    hdθU
  have hF₁ := fiberHyp_line Td endpoint_line_e₁ latL0_le latL0_le_e₁ z w y hw ωU hωU hdωU θU hθU
    hdθU
  obtain ⟨K, ν, hP⟩ := exists_primitives hF₀ stab latL0.topVanishingThree
  rw [lineValue_zero_eq Td z w y K hP.K_inv hP.K_d,
    show cycleT = cusp (prismData RationalGL3) latL0.σ isLevi_T from rfl,
    show cycleL = cusp (prismData RationalGL3) latL0.σ isLevi_L from rfl,
    pair_cusp_eq hF₀ hP (prismData RationalGL3) latL0.boundary_σ isLevi_T isLevi_T_inv
      T_mem_levelStabilizer_e₀,
    pair_cusp_eq hF₁ hP (prismData RationalGL3) latL0.boundary_σ isLevi_L isLevi_L_inv
      L_mem_levelStabilizer_e₁]
  have dT : defectValue (rationalCoefficientComponent n χ) Td.B latL0.σ ωU θU ν Tm =
      defectValue (rationalCoefficientComponent n χ) Td.B latL0.σ ωU θU ν (Tm * L⁻¹) +
        defectValue (rationalCoefficientComponent n χ) Td.B latL0.σ ωU θU ν L +
        kostant Td.B latL0.σ (pull1 (rationalCoefficientComponent n χ) L
          (leviCocycle (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹)))
          (leviCocycle (dualRep Td) θU L) := by
    have h := defectValue_mul hF₀ hP (prismData RationalGL3) latL0.boundary_σ isLevi_cone0_inv
      isLevi_L_inv
    rw [← T_eq_cone0] at h
    exact h
  have d2 : (0 : ℂ) =
      defectValue (rationalCoefficientComponent n χ) Td.B latL0.σ ωU θU ν (Tm * L⁻¹)⁻¹ +
        defectValue (rationalCoefficientComponent n χ) Td.B latL0.σ ωU θU ν (Tm * L⁻¹) +
        kostant Td.B latL0.σ (pull1 (rationalCoefficientComponent n χ) (Tm * L⁻¹)
          (leviCocycle (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹)⁻¹))
          (leviCocycle (dualRep Td) θU (Tm * L⁻¹)) := by
    have h := defectValue_mul hF₀ hP (prismData RationalGL3) latL0.boundary_σ
      isLevi_cone0_inv_inv isLevi_cone0_inv
    rw [inv_mul_cancel, defectValue_one] at h
    exact h
  have d3 := defectValue_torsion hF₀ hP (prismData RationalGL3) latL0.boundary_σ
    isLevi_cone0_inv_inv cone0_inv_pow_three
  push_cast at d3
  linear_combination -dT + d2 + (1 / 3 : ℂ) * d3

/-- **The local value at the bad line is the parabolic cup formula** of the crossed
homomorphisms `α(g) = g · ω_U − ω_U`, `β(g) = g · θ_U − θ_U` at the special elements `T`, `L⁻¹`,
`(T L⁻¹)⁻¹` of `Γ₁(3)`, with the Kostant pairing as coefficient pairing, the cusp primitives
`−c₀`, `−c₁` and the torsion primitive `−⅓ Σ_{j<3} A((T L⁻¹)^{-j})`. -/
theorem lineValue_badLine_cupFormula (Td : DualityData n χ) (z : MaximalCycles n χ .line)
    (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane) (hw : EdgePrimitive z w)
    (stab : IsTopVanishing (levelStabilizer L₀))
    (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL0.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n χ γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀)
    (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hθU : ∀ γ ∈ latL0.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n χ (Td.φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![Td.φ a, Td.φ b, Td.φ c] (Td.dualFlag L₀)) :
    lineValue traceDataL2 Td 0 z w y =
      cupFormula (kostantForm Td.B latL0.σ) (cochainRep (dualRep Td)) Tm L⁻¹
        (fun g => leviCocycle (rationalCoefficientComponent n χ) ωU g⁻¹)
        (fun g => leviCocycle (dualRep Td) θU g⁻¹)
        (-((fun x => w.val x e₀) - ωU), -((fun x => w.val x e₁) - ωU),
          -(1 / 3 : ℂ) • ∑ j ∈ Finset.range 3,
            leviCocycle (rationalCoefficientComponent n χ) ωU ((Tm * L⁻¹)⁻¹ ^ j)) := by
  have hF₀ := fiberHyp_line Td endpoint_line_e₀ latL0_le latL0_le_e₀ z w y hw ωU hωU hdωU θU hθU
    hdθU
  have hF₁ := fiberHyp_line Td endpoint_line_e₁ latL0_le latL0_le_e₁ z w y hw ωU hωU hdωU θU hθU
    hdθU
  have hB := hF₀.invariant
  have hUΛ := hF₀.le
  have hσ := latL0.boundary_σ
  rw [lineValue_badLine Td z w y hw stab ωU hωU hdωU θU hθU hdθU]
  -- the unfolded cup formula
  have e : cupFormula (kostantForm Td.B latL0.σ) (cochainRep (dualRep Td)) Tm L⁻¹
        (fun g => leviCocycle (rationalCoefficientComponent n χ) ωU g⁻¹)
        (fun g => leviCocycle (dualRep Td) θU g⁻¹)
        (-((fun x => w.val x e₀) - ωU), -((fun x => w.val x e₁) - ωU),
          -(1 / 3 : ℂ) • ∑ j ∈ Finset.range 3,
            leviCocycle (rationalCoefficientComponent n χ) ωU ((Tm * L⁻¹)⁻¹ ^ j)) =
      kostant Td.B latL0.σ (leviCocycle (rationalCoefficientComponent n χ) ωU Tm⁻¹)
          (pull1 (dualRep Td) Tm⁻¹ (leviCocycle (dualRep Td) θU L)) +
        kostant Td.B latL0.σ (leviCocycle (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹)⁻¹)
          (pull1 (dualRep Td) (Tm * L⁻¹)⁻¹ (leviCocycle (dualRep Td) θU (Tm * L⁻¹))) -
        (kostant Td.B latL0.σ (-((fun x => w.val x e₀) - ωU))
            (leviCocycle (dualRep Td) θU Tm⁻¹) +
          kostant Td.B latL0.σ (-((fun x => w.val x e₁) - ωU)) (leviCocycle (dualRep Td) θU L) +
          kostant Td.B latL0.σ (-(1 / 3 : ℂ) • ∑ j ∈ Finset.range 3,
              leviCocycle (rationalCoefficientComponent n χ) ωU ((Tm * L⁻¹)⁻¹ ^ j))
            (leviCocycle (dualRep Td) θU (Tm * L⁻¹))) := by
    simp only [cupFormula, kostantForm_apply, cochainRep_apply, inv_inv]
  -- the cocycle facts
  have hAT := (uCocycle_leviCocycle hF₀ isLevi_T_inv).1
  have hA'T := (uCocycle_leviCocycle hF₀ isLevi_T_inv).2
  have hA'L := (uCocycle_leviCocycle hF₀ isLevi_L_inv).2
  have hAg := (uCocycle_leviCocycle hF₀ isLevi_cone0_inv_inv).1
  have hA'g := (uCocycle_leviCocycle hF₀ isLevi_cone0_inv_inv).2
  have hc₀ := uCocycle_cusp hF₀
  -- the terms of the cup formula
  have F1 : kostant Td.B latL0.σ (leviCocycle (rationalCoefficientComponent n χ) ωU Tm⁻¹)
        (pull1 (dualRep Td) Tm⁻¹ (leviCocycle (dualRep Td) θU L)) =
      -kostant Td.B latL0.σ (leviCocycle (rationalCoefficientComponent n χ) ωU Tm)
        (leviCocycle (dualRep Td) θU L) := by
    rw [leviCocycle_inv (rationalCoefficientComponent n χ) ωU Tm, kostant_neg_left,
      kostant_pull1 (prismData RationalGL3) hσ hB hUΛ isLevi_T_inv_inv hAT hA'L]
  have F2 : kostant Td.B latL0.σ
        (leviCocycle (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹)⁻¹)
        (pull1 (dualRep Td) (Tm * L⁻¹)⁻¹ (leviCocycle (dualRep Td) θU (Tm * L⁻¹))) =
      -kostant Td.B latL0.σ (leviCocycle (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹)⁻¹)
        (leviCocycle (dualRep Td) θU (Tm * L⁻¹)⁻¹) := by
    rw [leviCocycle_eq_neg_pull1_inv (dualRep Td) θU (Tm * L⁻¹), pull1_neg, pull1_mul,
      mul_inv_cancel, pull1_one, kostant_neg_right]
  have F3 : kostant Td.B latL0.σ (-((fun x => w.val x e₀) - ωU))
        (leviCocycle (dualRep Td) θU Tm⁻¹) =
      kostant Td.B latL0.σ (pull1 (rationalCoefficientComponent n χ) Tm
          ((fun x => w.val x e₀) - ωU)) (leviCocycle (dualRep Td) θU Tm) := by
    rw [kostant_neg_left, leviCocycle_inv (dualRep Td) θU Tm, kostant_neg_right, neg_neg,
      kostant_shift (prismData RationalGL3) hσ hB hUΛ isLevi_T_inv isLevi_T_inv_inv hc₀ hA'T,
      inv_inv]
  have F4 : kostant Td.B latL0.σ (-((fun x => w.val x e₁) - ωU))
        (leviCocycle (dualRep Td) θU L) =
      -kostant Td.B latL0.σ ((fun x => w.val x e₁) - ωU) (leviCocycle (dualRep Td) θU L) :=
    kostant_neg_left _ _ _ _
  have F5 : kostant Td.B latL0.σ (-(1 / 3 : ℂ) • ∑ j ∈ Finset.range 3,
          leviCocycle (rationalCoefficientComponent n χ) ωU ((Tm * L⁻¹)⁻¹ ^ j))
        (leviCocycle (dualRep Td) θU (Tm * L⁻¹)) =
      (1 / 3 : ℂ) * ∑ j ∈ Finset.range 3, kostant Td.B latL0.σ
        (pull1 (rationalCoefficientComponent n χ) (Tm * L⁻¹)⁻¹
          (leviCocycle (rationalCoefficientComponent n χ) ωU ((Tm * L⁻¹)⁻¹ ^ j)))
        (leviCocycle (dualRep Td) θU (Tm * L⁻¹)⁻¹) := by
    have hsum : ∑ j ∈ Finset.range 3, kostant Td.B latL0.σ
          (leviCocycle (rationalCoefficientComponent n χ) ωU ((Tm * L⁻¹)⁻¹ ^ j))
          (pull1 (dualRep Td) (Tm * L⁻¹) (leviCocycle (dualRep Td) θU (Tm * L⁻¹)⁻¹)) =
        ∑ j ∈ Finset.range 3, kostant Td.B latL0.σ
          (pull1 (rationalCoefficientComponent n χ) (Tm * L⁻¹)⁻¹
            (leviCocycle (rationalCoefficientComponent n χ) ωU ((Tm * L⁻¹)⁻¹ ^ j)))
          (leviCocycle (dualRep Td) θU (Tm * L⁻¹)⁻¹) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [kostant_shift (prismData RationalGL3) hσ hB hUΛ isLevi_cone0 isLevi_cone0_inv
        (uCocycle_leviCocycle hF₀ (isLevi_pow_inv0 isLevi_cone0_inv_inv j)).1 hA'g]
    rw [leviCocycle_eq_neg_pull1_inv (dualRep Td) θU (Tm * L⁻¹), kostant_neg_right,
      kostant_smul_left, kostant_sum_left, hsum]
    ring
  have F7 : kostant Td.B latL0.σ (pull1 (rationalCoefficientComponent n χ) L
        ((fun x => w.val x e₁) - ωU)) (leviCocycle (dualRep Td) θU L) =
      kostant Td.B latL0.σ ((fun x => w.val x e₁) - ωU) (leviCocycle (dualRep Td) θU L) -
        kostant Td.B latL0.σ (leviCocycle (rationalCoefficientComponent n χ) ωU L)
          (leviCocycle (dualRep Td) θU L) := by
    rw [pull1_cusp hF₁ L_mem_levelStabilizer_e₁, kostant_sub_left]
  have F8 : kostant Td.B latL0.σ (leviCocycle (rationalCoefficientComponent n χ) ωU Tm)
        (leviCocycle (dualRep Td) θU L) =
      kostant Td.B latL0.σ (leviCocycle (rationalCoefficientComponent n χ) ωU L)
          (leviCocycle (dualRep Td) θU L) +
        kostant Td.B latL0.σ (pull1 (rationalCoefficientComponent n χ) L
          (leviCocycle (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹)))
          (leviCocycle (dualRep Td) θU L) := by
    have h := leviCocycle_mul (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹) L
    rw [← T_eq_cone0] at h
    rw [h, kostant_add_left]
  have F9 : kostant Td.B latL0.σ (pull1 (rationalCoefficientComponent n χ) (Tm * L⁻¹)
        (leviCocycle (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹)⁻¹))
        (leviCocycle (dualRep Td) θU (Tm * L⁻¹)) =
      -kostant Td.B latL0.σ (leviCocycle (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹)⁻¹)
        (leviCocycle (dualRep Td) θU (Tm * L⁻¹)⁻¹) := by
    rw [leviCocycle_eq_neg_pull1_inv (dualRep Td) θU (Tm * L⁻¹), kostant_neg_right,
      kostant_pull1 (prismData RationalGL3) hσ hB hUΛ isLevi_cone0_inv hAg hA'g]
  linear_combination -e - F1 - F2 + F3 + F4 + F5 + F7 + F8 + F9

end Value

end TernaryPeriodPolynomials.BoundaryDuality.FiberL0
