module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.LevelOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Primitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelOne

@[expose] public section


/-!
# The local value at the good line is a parabolic cup product of `GL₂(ℤ)`

At the good line `L₁` the local value of the boundary trace is minus the cup formula of the
crossed homomorphisms `α(g) = A(g⁻¹)`, `β(g) = A'(g⁻¹)` with values in the one-cochains, at the
special elements `S`, `T₀⁻¹`, `(S T₀⁻¹)⁻¹`, with the Kostant pairing `κ` as coefficient pairing
(`FiberLevelOne`). The triple `(−¼ Σ_{j<4} A(S^j), −(ω − ω_U), −⅓ Σ_{j<3} A((S T₀⁻¹)^{-j}))`
is a primitive triple of `α` (`isPrimitive_goodLine`): the first and the last are torsion
averages, the middle one is the cusp primitive given by the edge primitive `ω`.

A **level-one bridge** (`LevelOneBridge`) is a model `M`, `M'` of the coefficients `H¹(U, ·)` as
representations of `GL₂(ℤ)`: a Levi embedding `GL₂(ℤ) → GL₃(ℚ)` sending `S`, `T` to `S`, `T₀`,
linear maps `Φ`, `Ψ` from one-cochains to `M`, `M'` which are equivariant on `U`-equivariant
one-cocycles and carry the Levi cocycles to one-cocycles `x`, `x'` of `GL₂(ℤ)`, and a constant `c`
with `κ(f, g) = c · B(Φ f, Ψ g)` on `U`-equivariant one-cocycles (the Kostant identity). Given a
bridge, with `x`, `x'` parabolic and `B` satisfying the hypotheses of parabolic Poincaré duality,

  `lineValue = −c · ⟨[x], [x']⟩_par`

(`lineValue_goodLine_parabolicPairing`), the parabolic cup pairing of `GL₂(ℤ)` of
`ParabolicDuality.LevelOne`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.FiberParabolic

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.TopVanishing (IsTopVanishing)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal
open TernaryPeriodPolynomials.BoundaryDuality.ChiHom
open TernaryPeriodPolynomials.BoundaryDuality.CocycleBridge
  (cupFormula IsPrimitive)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
  (S T₀ L₁ e₂ T₀_mem_levelStabilizer_e₂)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant
open TernaryPeriodPolynomials.BoundaryDuality.FiberPrimitive
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1
open TernaryPeriodPolynomials.BoundaryDuality.FiberLevelOne
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (GL2Z toGL TwistedPairing parabolicCocycles parabolicPairing parabolicPairing_apply projectH1
    cocycleInclusion)

variable {n : ℕ} {χ : RankOneCharacter}

section Primitive

variable {T : DualityData n χ} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- The torsion primitive at `S`. -/
def primS (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n) :
    (Fin 2 → RationalGL3) → HomogeneousPoly n :=
  -(1 / 4 : ℂ) • ∑ j ∈ Finset.range 4,
    leviCocycle (rationalCoefficientComponent n χ) ωU (S ^ j)

/-- The torsion primitive at the inverse cone point `(S T₀⁻¹)⁻¹`. -/
def primE (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n) :
    (Fin 2 → RationalGL3) → HomogeneousPoly n :=
  -(1 / 3 : ℂ) • ∑ j ∈ Finset.range 3,
    leviCocycle (rationalCoefficientComponent n χ) ωU ((S * T₀⁻¹)⁻¹ ^ j)

/-- **The primitive triple at the good line.** -/
theorem isPrimitive_goodLine
    (hF : FiberHyp (rationalCoefficientComponent n χ) (dualRep T) T.B (levelStabilizer L₁)
      (levelStabilizer e₂) latL1.sub ζ η ω ωU θU) :
    IsPrimitive (cochainRep (rationalCoefficientComponent n χ)) S T₀⁻¹
      (fun g => leviCocycle (rationalCoefficientComponent n χ) ωU g⁻¹)
      (primS (χ := χ) ωU, -(ω - ωU), primE (χ := χ) ωU) := by
  refine ⟨?_, ?_, ?_⟩
  · show leviCocycle (rationalCoefficientComponent n χ) ωU S⁻¹ =
      cochainRep (rationalCoefficientComponent n χ) S (primS (χ := χ) ωU) - primS (χ := χ) ωU
    exact leviCocycle_torsion_primitive (rationalCoefficientComponent n χ) ωU (N := 3)
      S_pow_four (by norm_num)
  · show leviCocycle (rationalCoefficientComponent n χ) ωU T₀⁻¹⁻¹ =
      cochainRep (rationalCoefficientComponent n χ) T₀⁻¹ (-(ω - ωU)) - -(ω - ωU)
    rw [cochainRep_apply, inv_inv, pull1_neg, pull1_cusp hF T₀_mem_levelStabilizer_e₂]
    abel
  · show leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹⁻¹ =
      cochainRep (rationalCoefficientComponent n χ) (S * T₀⁻¹)⁻¹ (primE (χ := χ) ωU) -
        primE (χ := χ) ωU
    exact leviCocycle_torsion_primitive (rationalCoefficientComponent n χ) ωU (N := 2)
      cone_inv_pow_three (by norm_num)

/-- The torsion primitive at `S` is a `U`-equivariant one-cocycle. -/
theorem uCocycle_primS
    (hF : FiberHyp (rationalCoefficientComponent n χ) (dualRep T) T.B (levelStabilizer L₁)
      (levelStabilizer e₂) latL1.sub ζ η ω ωU θU) :
    UCocycle (rationalCoefficientComponent n χ) latL1.sub (primS (χ := χ) ωU) := by
  apply mem_uCocycles.mp
  unfold primS
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
    mem_uCocycles.mpr (uCocycle_leviCocycle hF (isLevi_pow_inv isLevi_S_inv j)).1)

/-- The torsion primitive at the inverse cone point is a `U`-equivariant one-cocycle. -/
theorem uCocycle_primE
    (hF : FiberHyp (rationalCoefficientComponent n χ) (dualRep T) T.B (levelStabilizer L₁)
      (levelStabilizer e₂) latL1.sub ζ η ω ωU θU) :
    UCocycle (rationalCoefficientComponent n χ) latL1.sub (primE (χ := χ) ωU) := by
  apply mem_uCocycles.mp
  unfold primE
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
    mem_uCocycles.mpr (uCocycle_leviCocycle hF (isLevi_pow_inv isLevi_cone_inv_inv j)).1)

/-- The cusp primitive is a `U`-equivariant one-cocycle. -/
theorem uCocycle_primCusp
    (hF : FiberHyp (rationalCoefficientComponent n χ) (dualRep T) T.B (levelStabilizer L₁)
      (levelStabilizer e₂) latL1.sub ζ η ω ωU θU) :
    UCocycle (rationalCoefficientComponent n χ) latL1.sub (-(ω - ωU)) :=
  mem_uCocycles.mp (Submodule.neg_mem _ (mem_uCocycles.mpr (uCocycle_cusp hF)))

end Primitive

/-- **A level-one bridge**: a model `M`, `M'` of the coefficients of the Levi cocycles at the good
line as representations of `GL₂(ℤ)`, through a Levi embedding, linear coordinate maps `Φ`, `Ψ`
equivariant on `U`-equivariant one-cocycles, one-cocycles `x`, `x'` of `GL₂(ℤ)` which are the
coordinates of the Levi cocycles, and the Kostant identity `κ(f, g) = c · B(Φ f, Ψ g)`. -/
structure LevelOneBridge (T : DualityData n χ) (ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (M M' : Rep.{0, 0, 0} ℂ GL2Z) (B₂ : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ)
    (x : groupCohomology.cocycles₁ M) (x' : groupCohomology.cocycles₁ M') (c : ℂ) where
  /-- The Levi embedding. -/
  levi : GL2Z →* RationalGL3
  /-- The coordinates of the line coefficients. -/
  Φ : ((Fin 2 → RationalGL3) → HomogeneousPoly n) →ₗ[ℂ] M
  /-- The coordinates of the dual coefficients. -/
  Ψ : ((Fin 2 → RationalGL3) → HomogeneousPoly n) →ₗ[ℂ] M'
  levi_S : levi (toGL ModularGroup.S) = S
  levi_T : levi (toGL ModularGroup.T) = T₀
  pairing : ∀ f g, UCocycle (rationalCoefficientComponent n χ) latL1.sub f →
    UCocycle (dualRep T) latL1.sub g → kostant T.B latL1.σ f g = c * B₂ (Φ f) (Ψ g)
  alpha : ∀ γ, Φ (leviCocycle (rationalCoefficientComponent n χ) ωU (levi γ)⁻¹) =
    cocycleInclusion M x γ
  beta : ∀ γ, Ψ (leviCocycle (dualRep T) θU (levi γ)⁻¹) = cocycleInclusion M' x' γ
  equivΦ : ∀ γ f, UCocycle (rationalCoefficientComponent n χ) latL1.sub f →
    Φ (cochainRep (rationalCoefficientComponent n χ) (levi γ) f) = M.ρ γ (Φ f)
  equivΨ : ∀ γ g, UCocycle (dualRep T) latL1.sub g →
    Ψ (cochainRep (dualRep T) (levi γ) g) = M'.ρ γ (Ψ g)

/-- **The local value at the good line is the parabolic cup pairing of `GL₂(ℤ)`**, through a
level-one bridge: `lineValue = −c · ⟨[x], [x']⟩_par`. -/
theorem lineValue_goodLine_parabolicPairing (T : DualityData n χ)
    (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane)
    (hw : EdgePrimitive z w) (stab : IsTopVanishing (levelStabilizer L₁))
    (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL1.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n χ γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₁)
    (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hθU : ∀ γ ∈ latL1.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n χ (T.φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![T.φ a, T.φ b, T.φ c] (T.dualFlag L₁))
    {M M' : Rep.{0, 0, 0} ℂ GL2Z} {B₂ : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ} (P : TwistedPairing M M' B₂)
    {x : groupCohomology.cocycles₁ M} {x' : groupCohomology.cocycles₁ M'}
    (hx : x ∈ parabolicCocycles M) (hx' : x' ∈ parabolicCocycles M') {c : ℂ}
    (Br : LevelOneBridge T ωU θU M M' B₂ x x' c) :
    lineValue traceDataL2 T 1 z w y =
      -c * parabolicPairing P ⟨projectH1 M x, Submodule.mem_map_of_mem hx⟩
        ⟨projectH1 M' x', Submodule.mem_map_of_mem hx'⟩ := by
  have hF := fiberHyp_goodLine T z w y hw ωU hωU hdωU θU hθU hdθU
  -- the Levi embedding at the special elements
  have lS : Br.levi (toGL ModularGroup.S) = S := Br.levi_S
  have lTi : Br.levi (toGL ModularGroup.T⁻¹) = T₀⁻¹ := by
    rw [map_inv, map_inv, Br.levi_T]
  have lST : Br.levi (toGL (ModularGroup.S * ModularGroup.T⁻¹)) = S * T₀⁻¹ := by
    rw [map_mul, map_mul, lS, lTi]
  have lSTi : Br.levi (toGL (ModularGroup.S * ModularGroup.T⁻¹)⁻¹) = (S * T₀⁻¹)⁻¹ := by
    rw [map_inv, map_inv, lST]
  -- the coordinates of the Levi cocycles
  have ezS : Br.Φ (leviCocycle (rationalCoefficientComponent n χ) ωU S⁻¹) =
      cocycleInclusion M x (toGL ModularGroup.S) := by
    rw [← Br.alpha, lS]
  have ezT : Br.Φ (leviCocycle (rationalCoefficientComponent n χ) ωU T₀⁻¹⁻¹) =
      cocycleInclusion M x (toGL ModularGroup.T⁻¹) := by
    rw [← Br.alpha, lTi]
  have ezST : Br.Φ (leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹) =
      cocycleInclusion M x (toGL (ModularGroup.S * ModularGroup.T⁻¹)) := by
    rw [← Br.alpha, lST]
  have ezSTi : Br.Φ (leviCocycle (rationalCoefficientComponent n χ) ωU (S * T₀⁻¹)⁻¹⁻¹) =
      cocycleInclusion M x (toGL (ModularGroup.S * ModularGroup.T⁻¹)⁻¹) := by
    rw [← Br.alpha, lSTi]
  have eyS : Br.Ψ (leviCocycle (dualRep T) θU S⁻¹) =
      cocycleInclusion M' x' (toGL ModularGroup.S) := by
    rw [← Br.beta, lS]
  have eyT : Br.Ψ (leviCocycle (dualRep T) θU T₀⁻¹⁻¹) =
      cocycleInclusion M' x' (toGL ModularGroup.T⁻¹) := by
    rw [← Br.beta, lTi]
  have eySTi : Br.Ψ (leviCocycle (dualRep T) θU (S * T₀⁻¹)⁻¹⁻¹) =
      cocycleInclusion M' x' (toGL (ModularGroup.S * ModularGroup.T⁻¹)⁻¹) := by
    rw [← Br.beta, lSTi]
  -- the cocycle facts
  have hAS := (uCocycle_leviCocycle hF isLevi_S_inv_inv).1
  have hAg := (uCocycle_leviCocycle hF isLevi_cone_inv_inv).1
  have hA'S := (uCocycle_leviCocycle hF isLevi_S_inv_inv).2
  have hA'T : UCocycle (dualRep T) latL1.sub (leviCocycle (dualRep T) θU T₀⁻¹⁻¹) :=
    (uCocycle_leviCocycle (σ := latL1.σ) hF (by simpa only [inv_inv] using isLevi_T₀_inv)).2
  have hA'E : UCocycle (dualRep T) latL1.sub (leviCocycle (dualRep T) θU (S * T₀⁻¹)⁻¹⁻¹) :=
    (uCocycle_leviCocycle (σ := latL1.σ) hF (by simpa only [inv_inv] using isLevi_cone_inv)).2
  have hY1 : UCocycle (dualRep T) latL1.sub
      (cochainRep (dualRep T) S (leviCocycle (dualRep T) θU T₀⁻¹⁻¹)) :=
    uCocycle_pull1 hA'T (inv_conj_mem_of_isLevi isLevi_S)
  have hY2 : UCocycle (dualRep T) latL1.sub
      (cochainRep (dualRep T) (S * T₀⁻¹) (leviCocycle (dualRep T) θU (S * T₀⁻¹)⁻¹⁻¹)) :=
    uCocycle_pull1 hA'E (conj_mem_of_isLevi_inv isLevi_cone_inv_inv)
  have hv1 := uCocycle_primS (χ := χ) hF
  have hv2 := uCocycle_primCusp hF
  have hv3 := uCocycle_primE (χ := χ) hF
  -- the equivariance of the coordinates at the special elements
  have q1 : Br.Φ (cochainRep (rationalCoefficientComponent n χ) S (primS (χ := χ) ωU)) =
      M.ρ (toGL ModularGroup.S) (Br.Φ (primS (χ := χ) ωU)) := by
    have h := Br.equivΦ (toGL ModularGroup.S) _ hv1
    rw [lS] at h
    exact h
  have q2 : Br.Φ (cochainRep (rationalCoefficientComponent n χ) T₀⁻¹ (-(edgeCochain w - ωU))) =
      M.ρ (toGL ModularGroup.T⁻¹) (Br.Φ (-(edgeCochain w - ωU))) := by
    have h := Br.equivΦ (toGL ModularGroup.T⁻¹) _ hv2
    rw [lTi] at h
    exact h
  have q3 : Br.Φ (cochainRep (rationalCoefficientComponent n χ) (S * T₀⁻¹)⁻¹
        (primE (χ := χ) ωU)) =
      M.ρ (toGL (ModularGroup.S * ModularGroup.T⁻¹)⁻¹) (Br.Φ (primE (χ := χ) ωU)) := by
    have h := Br.equivΦ (toGL (ModularGroup.S * ModularGroup.T⁻¹)⁻¹) _ hv3
    rw [lSTi] at h
    exact h
  have ey1 : Br.Ψ (cochainRep (dualRep T) S (leviCocycle (dualRep T) θU T₀⁻¹⁻¹)) =
      M'.ρ (toGL ModularGroup.S) (cocycleInclusion M' x' (toGL ModularGroup.T⁻¹)) := by
    have h := Br.equivΨ (toGL ModularGroup.S) _ hA'T
    rw [lS, eyT] at h
    exact h
  have ey2 : Br.Ψ (cochainRep (dualRep T) (S * T₀⁻¹)
        (leviCocycle (dualRep T) θU (S * T₀⁻¹)⁻¹⁻¹)) =
      M'.ρ (toGL (ModularGroup.S * ModularGroup.T⁻¹))
        (cocycleInclusion M' x' (toGL (ModularGroup.S * ModularGroup.T⁻¹)⁻¹)) := by
    have h := Br.equivΨ (toGL (ModularGroup.S * ModularGroup.T⁻¹)) _ hA'E
    rw [lST, eySTi] at h
    exact h
  -- the primitive triple of `x`
  have hv := isPrimitive_transfer (cochainRep (rationalCoefficientComponent n χ))
    (M.ρ.comp toGL) S T₀⁻¹ ModularGroup.S ModularGroup.T⁻¹
    (fun g => leviCocycle (rationalCoefficientComponent n χ) ωU g⁻¹)
    (fun g => cocycleInclusion M x (toGL g))
    (primS (χ := χ) ωU, -(edgeCochain w - ωU), primE (χ := χ) ωU) Br.Φ
    (isPrimitive_goodLine hF) ezS ezT ezSTi q1 q2 q3
  have key := cupFormula_transfer (kostantForm T.B latL1.σ) B₂ (cochainRep (dualRep T))
    (M'.ρ.comp toGL) S T₀⁻¹ ModularGroup.S ModularGroup.T⁻¹
    (fun g => leviCocycle (rationalCoefficientComponent n χ) ωU g⁻¹)
    (fun g => leviCocycle (dualRep T) θU g⁻¹)
    (fun g => cocycleInclusion M x (toGL g)) (fun g => cocycleInclusion M' x' (toGL g))
    (primS (χ := χ) ωU, -(edgeCochain w - ωU), primE (χ := χ) ωU) Br.Φ Br.Ψ c
    (Br.pairing _ _ hAS hY1) (Br.pairing _ _ hAg hY2) (Br.pairing _ _ hv1 hA'S)
    (Br.pairing _ _ hv2 hA'T) (Br.pairing _ _ hv3 hA'E) ezS ezST ey1 ey2 eyS eyT eySTi
  rw [lineValue_goodLine_cupFormula T z w y hw stab ωU hωU hdωU θU hθU hdθU,
    parabolicPairing_apply P x x' hx hx' hv,
    show (-(1 / 4 : ℂ) • ∑ j ∈ Finset.range 4,
        leviCocycle (rationalCoefficientComponent n χ) ωU (S ^ j)) = primS (χ := χ) ωU from rfl,
    show (-(1 / 3 : ℂ) • ∑ j ∈ Finset.range 3,
        leviCocycle (rationalCoefficientComponent n χ) ωU ((S * T₀⁻¹)⁻¹ ^ j)) =
      primE (χ := χ) ωU from rfl,
    key]
  ring

end TernaryPeriodPolynomials.BoundaryDuality.FiberParabolic
