module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level3Bridge

@[expose] public section


/-!
# Level three, bridge II: Eichler--Shimura for `core = Γ₁(3)` from the library's `Γ₁'(3)` results

Paper: Lemma C.3
(`ar:lem:seed`), Eichler--Shimura at the level-three plane cusp.

The library proves Eichler--Shimura for `Γ₁'(3) = Γ₁(3) ⊔ Γ₁(3) ε`, `ε = diag(-1, 1)`, with the
parity-projected period maps: `levelPeriodMap_range_eq_parabolic_of_injective` (injectivity is
`levelPeriodMap_injective_levelThree`) says that the image of `levelPeriodMap m e` is the parabolic
cohomology `H¹_par(Γ₁'(3), Sym^m ⊗ det^e)`, for every twist `e`. Extending the `±`
parts of a parabolic cocycle of `Γ₁(3)` to `Γ₁'(3)` with the twists `e` and `e + 1`
(`TwistSplitting.extendCocycle`), this gives `crossed_ES`: every parabolic cocycle of `core` is,
up to a coboundary, `(c + ι c)/2 + (c' - ι c')/2` for period cocycles `c`, `c'` of two cusp forms,
`ι c (k) = ρ(ε) c(ε k ε)`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups Manifold ModularForm
open GeneralEisenstein Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.LevelThree.TwistSplitting
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodDimension
open TernaryPeriodPolynomials.LevelThreeInjective.Main
  (levelPeriodMap_injective_levelThree)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel crossedCocycles crossedBoundaries crossedBoundary CrossedH1
   crossedPullbackH1 crossedPullbackH1_mk crossedPullbackCocycles)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper lower reflection)

open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive (V)

section CrossedES

variable (m : ℕ) (e : ℤ)

/-- The reflection-conjugate of a cocycle value: `ι z (k) = ρ(ε) z(ε k ε)`. -/
def iotaVal (z : crossedCocycles (coreRep m e)) (k : core) : V m :=
  levelRep m e reflection (z.val (conjH (fun _ hk => conj_mem_core hk) k))

/-- **Eichler--Shimura for `Γ₁(3)` from the library's `Γ₁'(3)` results.** Every parabolic
cocycle of `core` is, up to a coboundary, `(c + ι c)/2 + (c' - ι c')/2` for the period cocycles
`c`, `c'` of two cusp forms. -/
theorem crossed_ES (hm : 0 < m) (z : crossedCocycles (coreRep m e))
    (hz : z ∈ TwoGenerator.parabolicCocycles (coreRep m e) coreT coreL) :
    ∃ (f₀ f₁ : S m) (v : V m), ∀ k : core,
      z.val k = (2 : ℂ)⁻¹ • ((periodCocycle m e f₀).val k + iotaVal m e (periodCocycle m e f₀) k) +
        (2 : ℂ)⁻¹ • ((periodCocycle m e f₁).val k - iotaVal m e (periodCocycle m e f₁) k) +
        (coreRep m e k v - v) := by
  classical
  have hεε := reflection_mul_self
  have normal : ∀ k ∈ core, reflection * k * reflection ∈ core :=
    fun _ hk => conj_mem_core hk
  have agree : ∀ k : core, levelRep m (e + 1) k.val = levelRep m e k.val :=
    fun k => ExactLevel.twist_agree m e k
  have anti := ExactLevel.twist_anti m e
  let plus := extendCocycle (H := core) (ε := reflection) mem_core_or
    (levelRep m e) (levelRep m e) hεε normal (fun _ => rfl)
    (plusPart (levelRep m e) hεε normal z) (plusPart_conj (levelRep m e) hεε normal z)
  let minus := extendCocycle (H := core) (ε := reflection) mem_core_or
    (levelRep m e) (levelRep m (e + 1)) hεε normal agree
    (minusPart (levelRep m e) hεε normal z)
    (minusPart_conj (levelRep m e) (levelRep m (e + 1)) hεε normal anti z)
  have plusT := extendCocycle_mem (H := core) (ε := reflection) mem_core_or
    (levelRep m e) (levelRep m e) hεε normal (fun _ => rfl) _
    (plusPart_conj (levelRep m e) hεε normal z) coreT
  have plusL := extendCocycle_mem (H := core) (ε := reflection) mem_core_or
    (levelRep m e) (levelRep m e) hεε normal (fun _ => rfl) _
    (plusPart_conj (levelRep m e) hεε normal z) coreL
  have minusT := extendCocycle_mem (H := core) (ε := reflection) mem_core_or
    (levelRep m e) (levelRep m (e + 1)) hεε normal agree _
    (minusPart_conj (levelRep m e) (levelRep m (e + 1)) hεε normal anti z) coreT
  have minusL := extendCocycle_mem (H := core) (ε := reflection) mem_core_or
    (levelRep m e) (levelRep m (e + 1)) hεε normal agree _
    (minusPart_conj (levelRep m e) (levelRep m (e + 1)) hεε normal anti z) coreL
  have pp := plusPart_parabolic (levelRep m e) hεε normal (upper 1)
    (lower 1) coreT.property coreL.property SharpBounds.hεT SharpBounds.hεL
    z hz
  have mp := minusPart_parabolic (levelRep m e) hεε normal (upper 1)
    (lower 1) coreT.property coreL.property SharpBounds.hεT SharpBounds.hεL
    z hz
  have plus_mem : (crossedBoundaries (levelRep m e)).mkQ plus ∈
      TwoGenerator.parabolicH1 (levelRep m e) (upper 1)
        (lower 1) :=
    ⟨plus, ⟨by change plus.val coreT.val ∈ _; rw [plusT]; exact pp.1,
      by change plus.val coreL.val ∈ _; rw [plusL]; exact pp.2⟩, rfl⟩
  have minus_mem : (crossedBoundaries (levelRep m (e + 1))).mkQ minus ∈
      TwoGenerator.parabolicH1 (levelRep m (e + 1)) (upper 1)
        (lower 1) :=
    ⟨minus, ⟨by
      change minus.val coreT.val ∈ _
      rw [minusT, moved_agree (levelRep m e) (levelRep m (e + 1)) agree (upper 1) coreT.property]
      exact mp.1, by
      change minus.val coreL.val ∈ _
      rw [minusL, moved_agree (levelRep m e) (levelRep m (e + 1)) agree (lower 1) coreL.property]
      exact mp.2⟩, rfl⟩
  rw [← levelPeriodMap_range_eq_parabolic_of_injective hm
    (levelPeriodMap_injective_levelThree m e)] at plus_mem
  rw [← levelPeriodMap_range_eq_parabolic_of_injective hm
    (levelPeriodMap_injective_levelThree m (e + 1))] at minus_mem
  obtain ⟨f₀, hf₀⟩ := plus_mem
  obtain ⟨f₁, hf₁⟩ := minus_mem
  rw [levelPeriodMap_apply] at hf₀ hf₁
  have h0 := (Submodule.Quotient.eq _).1 hf₀
  have h1 := (Submodule.Quotient.eq _).1 hf₁
  obtain ⟨v₀, hv₀⟩ := h0
  obtain ⟨v₁, hv₁⟩ := h1
  refine ⟨f₀, f₁, -(v₀ + v₁), fun k => ?_⟩
  have e0 : levelRep m e k.val v₀ - v₀ =
      (levelPlus m e (periodCocycle m e f₀)).val k.val - plus.val k.val :=
    congrArg (fun c => c.val k.val) hv₀
  have e1 : levelRep m (e + 1) k.val v₁ - v₁ =
      (levelPlus m (e + 1) (periodCocycle m (e + 1) f₁)).val k.val - minus.val k.val :=
    congrArg (fun c => c.val k.val) hv₁
  rw [levelPlus_core] at e0 e1
  have p0 : plus.val k.val = (plusPart (levelRep m e) hεε normal z).val k :=
    extendCocycle_mem (H := core) (ε := reflection) mem_core_or
      (levelRep m e) (levelRep m e) hεε normal (fun _ => rfl) _
      (plusPart_conj (levelRep m e) hεε normal z) k
  have m0 : minus.val k.val = (minusPart (levelRep m e) hεε normal z).val k :=
    extendCocycle_mem (H := core) (ε := reflection) mem_core_or
      (levelRep m e) (levelRep m (e + 1)) hεε normal agree _
      (minusPart_conj (levelRep m e) (levelRep m (e + 1)) hεε normal anti z) k
  have hsum := congrArg (fun c => c.val k) (plus_add_minus (levelRep m e) hεε normal z)
  rw [p0] at e0
  rw [m0] at e1
  change (plusPart (levelRep m e) hεε normal z).val k +
    (minusPart (levelRep m e) hεε normal z).val k = z.val k at hsum
  have hP : (plusPart (levelRep m e) hεε normal (periodCocycle m e f₀)).val k =
      (2 : ℂ)⁻¹ • ((periodCocycle m e f₀).val k + iotaVal m e (periodCocycle m e f₀) k) := rfl
  have hP' : (plusPart (levelRep m (e + 1)) hεε normal (periodCocycle m (e + 1) f₁)).val k =
      (2 : ℂ)⁻¹ • ((periodCocycle m e f₁).val k - iotaVal m e (periodCocycle m e f₁) k) := by
    change (2 : ℂ)⁻¹ • ((periodCocycle m (e + 1) f₁).val k +
      levelRep m (e + 1) reflection
        ((periodCocycle m (e + 1) f₁).val (conjH normal k))) = _
    rw [anti, LinearMap.neg_apply, ← sub_eq_add_neg]
    rfl
  rw [hP] at e0
  rw [hP'] at e1
  rw [agree k] at e1
  change z.val k = _ + _ + ((levelRep m e k.val) (-(v₀ + v₁)) - -(v₀ + v₁))
  rw [map_neg, map_add]
  linear_combination (norm := module) e0 + e1 - hsum

end CrossedES

end TernaryPeriodPolynomials.Argument.SeedC3S4c
