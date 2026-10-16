module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.L0
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Primitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelThree

@[expose] public section


/-!
# The local value at the bad line is a parabolic cup product of `Γ₁'(3)`

At the bad line `L₀` the local value of the boundary trace is the cup formula of the crossed
homomorphisms `α(g) = A(g⁻¹)`, `β(g) = A'(g⁻¹)` with values in the one-cochains, at the special
elements `T`, `L⁻¹`, `(T L⁻¹)⁻¹` of `Γ₁(3)`, with the Kostant pairing as coefficient pairing
(`FiberL0`). The triple `(−c₀, −c₁, −⅓ Σ_{j<3} A((T L⁻¹)^{-j}))` of the two cusp primitives and
the torsion average is a primitive triple of `α` (`isPrimitive_badLine`).

A **level-three bridge** (`LevelThreeBridge`) is a model `V'`, `W'` of the coefficients as
representations of `Γ₁'(3)`: a Levi embedding `Γ₁'(3) → GL₃(ℚ)` sending `T`, `L` to the Levi
generators `T = I + E₁₂`, `L = I + 3E₂₁` of `L₀`, linear maps `Φ`, `Ψ` equivariant on
`U`-equivariant one-cocycles which carry the Levi cocycles to crossed homomorphisms `x`, `x'`
of `Γ₁'(3)`, and the Kostant identity `κ(f, g) = c · B(Φ f, Ψ g)`. Given a bridge, with `x`,
`x'` parabolic,

  `lineValue = c · ⟨[x], [x']⟩_par`

(`lineValue_badLine_parabolicPairing`), the parabolic cup pairing of `Γ₁'(3)` of
`ParabolicDuality.LevelThree`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.FiberParabolicL0

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.TopVanishing (IsTopVanishing)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal
open TernaryPeriodPolynomials.BoundaryDuality.ChiHom
open TernaryPeriodPolynomials.BoundaryDuality.CocycleBridge
  (cupFormula IsPrimitive)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
  (latL0 latL0_le latL0_le_e₀ latL0_le_e₁ isLevi_T isLevi_L)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
  (L L₀ e₀ e₁ T_mem_levelStabilizer_e₀ L_mem_levelStabilizer_e₁ endpoint_line_e₀
    endpoint_line_e₁)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant
open TernaryPeriodPolynomials.BoundaryDuality.FiberPrimitive
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL0
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel crossedCocycles crossedBoundaries)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper lower)
open TernaryPeriodPolynomials.LevelThree.GammaOneThree (core coreT coreL)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (TwistedPairing parabolicCrossed parabolicPairing parabolicPairing_apply)

/-- The unipotent Levi element `T = I + E₁₂` at the bad line. -/
local notation "Tm" => TernaryPeriodPolynomials.BoundaryDuality.L2Matrices.T

variable {n : ℕ} {χ : RankOneCharacter}

section Primitive

variable {Td : DualityData n χ} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω₀ ω₁ ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- The torsion primitive at the inverse cone point `(T L⁻¹)⁻¹`. -/
def primE0 (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n) :
    (Fin 2 → RationalGL3) → HomogeneousPoly n :=
  -(1 / 3 : ℂ) • ∑ j ∈ Finset.range 3,
    leviCocycle (rationalCoefficientComponent n χ) ωU ((Tm * L⁻¹)⁻¹ ^ j)

/-- **The primitive triple at the bad line.** -/
theorem isPrimitive_badLine
    (hF₀ : FiberHyp (rationalCoefficientComponent n χ) (dualRep Td) Td.B (levelStabilizer L₀)
      (levelStabilizer e₀) latL0.sub ζ η ω₀ ωU θU)
    (hF₁ : FiberHyp (rationalCoefficientComponent n χ) (dualRep Td) Td.B (levelStabilizer L₀)
      (levelStabilizer e₁) latL0.sub ζ η ω₁ ωU θU) :
    IsPrimitive (cochainRep (rationalCoefficientComponent n χ)) Tm L⁻¹
      (fun g => leviCocycle (rationalCoefficientComponent n χ) ωU g⁻¹)
      (-(ω₀ - ωU), -(ω₁ - ωU), primE0 (χ := χ) ωU) := by
  refine ⟨?_, ?_, ?_⟩
  · show leviCocycle (rationalCoefficientComponent n χ) ωU Tm⁻¹ =
      cochainRep (rationalCoefficientComponent n χ) Tm (-(ω₀ - ωU)) - -(ω₀ - ωU)
    have hA : leviCocycle (rationalCoefficientComponent n χ) ωU Tm =
        (ω₀ - ωU) - pull1 (rationalCoefficientComponent n χ) Tm (ω₀ - ωU) := by
      rw [pull1_cusp hF₀ T_mem_levelStabilizer_e₀]
      abel
    rw [leviCocycle_inv (rationalCoefficientComponent n χ) ωU Tm, hA,
      pull1_sub (rationalCoefficientComponent n χ) Tm⁻¹ (ω₀ - ωU)
        (pull1 (rationalCoefficientComponent n χ) Tm (ω₀ - ωU)),
      pull1_mul (rationalCoefficientComponent n χ) Tm Tm⁻¹ (ω₀ - ωU), mul_inv_cancel, pull1_one,
      cochainRep_apply, pull1_neg (rationalCoefficientComponent n χ) Tm⁻¹ (ω₀ - ωU)]
    abel
  · show leviCocycle (rationalCoefficientComponent n χ) ωU L⁻¹⁻¹ =
      cochainRep (rationalCoefficientComponent n χ) L⁻¹ (-(ω₁ - ωU)) - -(ω₁ - ωU)
    rw [cochainRep_apply, inv_inv, pull1_neg, pull1_cusp hF₁ L_mem_levelStabilizer_e₁]
    abel
  · show leviCocycle (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹)⁻¹⁻¹ =
      cochainRep (rationalCoefficientComponent n χ) (Tm * L⁻¹)⁻¹ (primE0 (χ := χ) ωU) -
        primE0 (χ := χ) ωU
    exact leviCocycle_torsion_primitive (rationalCoefficientComponent n χ) ωU (N := 2)
      cone0_inv_pow_three (by norm_num)

/-- The torsion primitive at the inverse cone point is a `U`-equivariant one-cocycle. -/
theorem uCocycle_primE0
    (hF₀ : FiberHyp (rationalCoefficientComponent n χ) (dualRep Td) Td.B (levelStabilizer L₀)
      (levelStabilizer e₀) latL0.sub ζ η ω₀ ωU θU) :
    UCocycle (rationalCoefficientComponent n χ) latL0.sub (primE0 (χ := χ) ωU) := by
  apply mem_uCocycles.mp
  unfold primE0
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
    mem_uCocycles.mpr (uCocycle_leviCocycle hF₀ (isLevi_pow_inv0 isLevi_cone0_inv_inv j)).1)

/-- The negated cusp primitive is a `U`-equivariant one-cocycle. -/
theorem uCocycle_negCusp {Λe : Subgroup RationalGL3} {ω : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : FiberHyp (rationalCoefficientComponent n χ) (dualRep Td) Td.B (levelStabilizer L₀)
      Λe latL0.sub ζ η ω ωU θU) :
    UCocycle (rationalCoefficientComponent n χ) latL0.sub (-(ω - ωU)) :=
  mem_uCocycles.mp (Submodule.neg_mem _ (mem_uCocycles.mpr (uCocycle_cusp hF)))

end Primitive

/-- **A level-three bridge**: a model `V'`, `W'` of the coefficients of the Levi cocycles at the
bad line as representations of `Γ₁'(3)`, through a Levi embedding, linear coordinate maps `Φ`, `Ψ`
equivariant on `U`-equivariant one-cocycles, crossed homomorphisms `x`, `x'` of `Γ₁'(3)` which are
the coordinates of the Levi cocycles, and the Kostant identity `κ(f, g) = c · B(Φ f, Ψ g)`. -/
structure LevelThreeBridge (Td : DualityData n χ)
    (ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n) {V' W' : Type} [AddCommGroup V']
    [Module ℂ V'] [AddCommGroup W'] [Module ℂ W'] (ρb : Representation ℂ binaryArithmeticLevel V')
    (ρb' : Representation ℂ binaryArithmeticLevel W') (B₂ : V' →ₗ[ℂ] W' →ₗ[ℂ] ℂ)
    (x : crossedCocycles ρb) (x' : crossedCocycles ρb') (c : ℂ) where
  /-- The Levi embedding. -/
  levi : binaryArithmeticLevel →* RationalGL3
  /-- The coordinates of the line coefficients. -/
  Φ : ((Fin 2 → RationalGL3) → HomogeneousPoly n) →ₗ[ℂ] V'
  /-- The coordinates of the dual coefficients. -/
  Ψ : ((Fin 2 → RationalGL3) → HomogeneousPoly n) →ₗ[ℂ] W'
  levi_T : levi (upper 1) = Tm
  levi_L : levi (lower 1) = L
  pairing : ∀ f g, UCocycle (rationalCoefficientComponent n χ) latL0.sub f →
    UCocycle (dualRep Td) latL0.sub g → kostant Td.B latL0.σ f g = c * B₂ (Φ f) (Ψ g)
  alpha : ∀ γ, Φ (leviCocycle (rationalCoefficientComponent n χ) ωU (levi γ)⁻¹) = x.1 γ
  beta : ∀ γ, Ψ (leviCocycle (dualRep Td) θU (levi γ)⁻¹) = x'.1 γ
  equivΦ : ∀ γ f, UCocycle (rationalCoefficientComponent n χ) latL0.sub f →
    Φ (cochainRep (rationalCoefficientComponent n χ) (levi γ) f) = ρb γ (Φ f)
  equivΨ : ∀ γ g, UCocycle (dualRep Td) latL0.sub g →
    Ψ (cochainRep (dualRep Td) (levi γ) g) = ρb' γ (Ψ g)

/-- **The local value at the bad line is the parabolic cup pairing of `Γ₁'(3)`**, through a
level-three bridge: `lineValue = c · ⟨[x], [x']⟩_par`. -/
theorem lineValue_badLine_parabolicPairing (Td : DualityData n χ)
    (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane)
    (hw : EdgePrimitive z w) (stab : IsTopVanishing (levelStabilizer L₀))
    (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL0.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n χ γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀)
    (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hθU : ∀ γ ∈ latL0.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n χ (Td.φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![Td.φ a, Td.φ b, Td.φ c] (Td.dualFlag L₀))
    {V' W' : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρb : Representation ℂ binaryArithmeticLevel V'}
    {ρb' : Representation ℂ binaryArithmeticLevel W'} {B₂ : V' →ₗ[ℂ] W' →ₗ[ℂ] ℂ}
    (P : TwistedPairing ρb ρb' B₂) {x : crossedCocycles ρb} {x' : crossedCocycles ρb'}
    (hx : x ∈ parabolicCrossed ρb) (hx' : x' ∈ parabolicCrossed ρb') {c : ℂ}
    (Br : LevelThreeBridge Td ωU θU ρb ρb' B₂ x x' c) :
    lineValue traceDataL2 Td 0 z w y =
      c * parabolicPairing P ⟨(crossedBoundaries ρb).mkQ x, Submodule.mem_map_of_mem hx⟩
        ⟨(crossedBoundaries ρb').mkQ x', Submodule.mem_map_of_mem hx'⟩ := by
  have hF₀ := fiberHyp_line Td endpoint_line_e₀ latL0_le latL0_le_e₀ z w y hw ωU hωU hdωU θU hθU
    hdθU
  have hF₁ := fiberHyp_line Td endpoint_line_e₁ latL0_le latL0_le_e₁ z w y hw ωU hωU hdωU θU hθU
    hdθU
  -- the Levi embedding at the special elements
  have lT : Br.levi (core.subtype coreT) = Tm := Br.levi_T
  have lLi : Br.levi (core.subtype coreL⁻¹) = L⁻¹ := by
    rw [map_inv, map_inv]
    show (Br.levi (lower 1))⁻¹ = L⁻¹
    rw [Br.levi_L]
  have lTL : Br.levi (core.subtype (coreT * coreL⁻¹)) = Tm * L⁻¹ := by
    rw [map_mul, map_mul, lT, lLi]
  have lTLi : Br.levi (core.subtype (coreT * coreL⁻¹)⁻¹) = (Tm * L⁻¹)⁻¹ := by
    rw [map_inv, map_inv, lTL]
  -- the coordinates of the Levi cocycles
  have ezT : Br.Φ (leviCocycle (rationalCoefficientComponent n χ) ωU Tm⁻¹) =
      x.1 (core.subtype coreT) := by
    rw [← Br.alpha, lT]
  have ezL : Br.Φ (leviCocycle (rationalCoefficientComponent n χ) ωU L⁻¹⁻¹) =
      x.1 (core.subtype coreL⁻¹) := by
    rw [← Br.alpha, lLi]
  have ezTL : Br.Φ (leviCocycle (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹)⁻¹) =
      x.1 (core.subtype (coreT * coreL⁻¹)) := by
    rw [← Br.alpha, lTL]
  have ezTLi : Br.Φ (leviCocycle (rationalCoefficientComponent n χ) ωU (Tm * L⁻¹)⁻¹⁻¹) =
      x.1 (core.subtype (coreT * coreL⁻¹)⁻¹) := by
    rw [← Br.alpha, lTLi]
  have eyT : Br.Ψ (leviCocycle (dualRep Td) θU Tm⁻¹) = x'.1 (core.subtype coreT) := by
    rw [← Br.beta, lT]
  have eyL : Br.Ψ (leviCocycle (dualRep Td) θU L⁻¹⁻¹) = x'.1 (core.subtype coreL⁻¹) := by
    rw [← Br.beta, lLi]
  have eyTLi : Br.Ψ (leviCocycle (dualRep Td) θU (Tm * L⁻¹)⁻¹⁻¹) =
      x'.1 (core.subtype (coreT * coreL⁻¹)⁻¹) := by
    rw [← Br.beta, lTLi]
  -- the cocycle facts
  have hAT := (uCocycle_leviCocycle hF₀ isLevi_T_inv_inv).1
  have hAg := (uCocycle_leviCocycle hF₀ isLevi_cone0_inv_inv).1
  have hA'T := (uCocycle_leviCocycle hF₀ isLevi_T_inv_inv).2
  have hA'L : UCocycle (dualRep Td) latL0.sub (leviCocycle (dualRep Td) θU L⁻¹⁻¹) :=
    (uCocycle_leviCocycle (σ := latL0.σ) hF₀ (by simpa only [inv_inv] using isLevi_L_inv)).2
  have hA'E : UCocycle (dualRep Td) latL0.sub (leviCocycle (dualRep Td) θU (Tm * L⁻¹)⁻¹⁻¹) :=
    (uCocycle_leviCocycle (σ := latL0.σ) hF₀ (by simpa only [inv_inv] using isLevi_cone0_inv)).2
  have hY1 : UCocycle (dualRep Td) latL0.sub
      (cochainRep (dualRep Td) Tm (leviCocycle (dualRep Td) θU L⁻¹⁻¹)) :=
    uCocycle_pull1 hA'L (inv_conj_mem_of_isLevi isLevi_T)
  have hY2 : UCocycle (dualRep Td) latL0.sub
      (cochainRep (dualRep Td) (Tm * L⁻¹) (leviCocycle (dualRep Td) θU (Tm * L⁻¹)⁻¹⁻¹)) :=
    uCocycle_pull1 hA'E (conj_mem_of_isLevi_inv isLevi_cone0_inv_inv)
  have hv1 := uCocycle_negCusp hF₀
  have hv2 := uCocycle_negCusp hF₁
  have hv3 := uCocycle_primE0 (χ := χ) hF₀
  -- the equivariance of the coordinates at the special elements
  have q1 : Br.Φ (cochainRep (rationalCoefficientComponent n χ) Tm
        (-((fun x => w.val x e₀) - ωU))) =
      ρb (core.subtype coreT) (Br.Φ (-((fun x => w.val x e₀) - ωU))) := by
    have h := Br.equivΦ (core.subtype coreT) _ hv1
    rw [lT] at h
    exact h
  have q2 : Br.Φ (cochainRep (rationalCoefficientComponent n χ) L⁻¹
        (-((fun x => w.val x e₁) - ωU))) =
      ρb (core.subtype coreL⁻¹) (Br.Φ (-((fun x => w.val x e₁) - ωU))) := by
    have h := Br.equivΦ (core.subtype coreL⁻¹) _ hv2
    rw [lLi] at h
    exact h
  have q3 : Br.Φ (cochainRep (rationalCoefficientComponent n χ) (Tm * L⁻¹)⁻¹
        (primE0 (χ := χ) ωU)) =
      ρb (core.subtype (coreT * coreL⁻¹)⁻¹) (Br.Φ (primE0 (χ := χ) ωU)) := by
    have h := Br.equivΦ (core.subtype (coreT * coreL⁻¹)⁻¹) _ hv3
    rw [lTLi] at h
    exact h
  have ey1 : Br.Ψ (cochainRep (dualRep Td) Tm (leviCocycle (dualRep Td) θU L⁻¹⁻¹)) =
      ρb' (core.subtype coreT) (x'.1 (core.subtype coreL⁻¹)) := by
    have h := Br.equivΨ (core.subtype coreT) _ hA'L
    rw [lT, eyL] at h
    exact h
  have ey2 : Br.Ψ (cochainRep (dualRep Td) (Tm * L⁻¹)
        (leviCocycle (dualRep Td) θU (Tm * L⁻¹)⁻¹⁻¹)) =
      ρb' (core.subtype (coreT * coreL⁻¹)) (x'.1 (core.subtype (coreT * coreL⁻¹)⁻¹)) := by
    have h := Br.equivΨ (core.subtype (coreT * coreL⁻¹)) _ hA'E
    rw [lTL, eyTLi] at h
    exact h
  -- the primitive triple of `x`
  have hv := isPrimitive_transfer (cochainRep (rationalCoefficientComponent n χ))
    (ρb.comp core.subtype) Tm L⁻¹ coreT coreL⁻¹
    (fun g => leviCocycle (rationalCoefficientComponent n χ) ωU g⁻¹)
    (fun g => x.1 (core.subtype g))
    (-((fun x => w.val x e₀) - ωU), -((fun x => w.val x e₁) - ωU), primE0 (χ := χ) ωU) Br.Φ
    (isPrimitive_badLine hF₀ hF₁) ezT ezL ezTLi q1 q2 q3
  have key := cupFormula_transfer (kostantForm Td.B latL0.σ) B₂ (cochainRep (dualRep Td))
    (ρb'.comp core.subtype) Tm L⁻¹ coreT coreL⁻¹
    (fun g => leviCocycle (rationalCoefficientComponent n χ) ωU g⁻¹)
    (fun g => leviCocycle (dualRep Td) θU g⁻¹)
    (fun g => x.1 (core.subtype g)) (fun g => x'.1 (core.subtype g))
    (-((fun x => w.val x e₀) - ωU), -((fun x => w.val x e₁) - ωU), primE0 (χ := χ) ωU)
    Br.Φ Br.Ψ c
    (Br.pairing _ _ hAT hY1) (Br.pairing _ _ hAg hY2) (Br.pairing _ _ hv1 hA'T)
    (Br.pairing _ _ hv2 hA'L) (Br.pairing _ _ hv3 hA'E) ezT ezTL ey1 ey2 eyT eyL eyTLi
  rw [lineValue_badLine_cupFormula Td z w y hw stab ωU hωU hdωU θU hθU hdθU,
    parabolicPairing_apply P x x' hx hx' hv,
    show (-(1 / 3 : ℂ) • ∑ j ∈ Finset.range 3,
        leviCocycle (rationalCoefficientComponent n χ) ωU ((Tm * L⁻¹)⁻¹ ^ j)) =
      primE0 (χ := χ) ωU from rfl]
  exact key

end TernaryPeriodPolynomials.BoundaryDuality.FiberParabolicL0
