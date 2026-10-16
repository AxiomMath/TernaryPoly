module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Cosets

@[expose] public section


/-!
# Hecke operators on `H¹(Γ₁'(3), Sym^m ⊗ det^e)` and `H¹(Γ₁(3), Sym^m ⊗ det^e)`

All cohomology here is Sol's crossed-cocycle model `CrossedH1 ρ` (cocycles
`c(gh) = c(g) + ρ(g) c(h)` modulo `g ↦ ρ(g) v - v`), the model in which every level-three result (`ExactLevel`, `BadLineLocal.badLineLeviMap`) is stated.

*Generic part.* For `RightCosets` data `G α_j` of `G ⊆ 𝔾` (`HeckeH1.RightCosets`, transitions
`α_j g = δ(g, j) α_{next g j}`) and a representation `σ` of `𝔾` restricting to `ρ` on `G`,
`(T c)(g) = ∑_j σ(α_j)⁻¹ c(δ(g, j))`
maps crossed cocycles to crossed cocycles and boundaries to boundaries (`crossedHeckeCocycles`),
hence acts on `CrossedH1 ρ` (`crossedHecke`, `crossedHecke_mk`). Restriction along a subgroup with
the same representatives and compatible transitions intertwines the operators
(`pullback_crossedHecke`), and the Hecke trace of a primitive is a primitive of `T c`
(`crossedHeckeFun_primitive`).

*Level three.* With the `p + 1` cosets of `LevelThreeCosets` (`α_j = [[1, j], [0, p]]`,
`α_∞ = ε_p [[p, 0], [0, 1]]`, `ε_p ≡ p mod 3`, `p ≠ 3`) and `σ = Sym^m ⊗ det^e` of `GL₂(ℚ)`:

* `levelHecke m e p hp3 : Module.End ℂ (CrossedH1 (levelRep m e))` (`Γ₁'(3)`),
  `(T c)(g) = ∑_j σ(α_j)⁻¹ c(α_j g α_{next g j}⁻¹)` (`levelHecke_mk`);
* `coreHecke m e p hp3 : Module.End ℂ (CrossedH1 (coreRep m e))` (`Γ₁(3)`, same formula);
* `restriction_levelHecke`: `res ∘ levelHecke = coreHecke ∘ res`
  (`res = ParabolicBounds.restriction`);
* `badLevelHecke n p hp3 : Module.End ℂ (CrossedH1 (binaryArithmeticRepresentation n))`, the
  operator on the codomain of `BadLineLocal.badLineLeviMap` (`= levelHecke (n + 1) 0`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers GammaOneThree ParabolicBounds LevelThreeCosets
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.Spectral.LevelOneCosets
open GeneralEisenstein

section Generic

variable {G 𝔾 V : Type} [Group G] [Group 𝔾] [AddCommGroup V] [Module ℂ V]
  {embed : G →* 𝔾} (S : RightCosets embed) (σ : Representation ℂ 𝔾 V)
  (ρ : Representation ℂ G V) (compat : ∀ g, ρ g = σ (embed g))
  (embedded : Function.Injective embed)

/-- The Hecke formula `(T c)(g) = ∑_j σ(α_j)⁻¹ c(δ(g, j))` on functions `G → V`. -/
def crossedHeckeFun (c : G → V) (g : G) : V :=
  ∑ j, σ (S.rep j)⁻¹ (c (S.delta g j))

theorem crossedHeckeFun_apply (c : G → V) (g : G) :
    crossedHeckeFun S σ c g = ∑ j, σ (S.rep j)⁻¹ (c (S.delta g j)) := rfl

include compat embedded in
theorem crossedHeckeFun_mem (c : crossedCocycles ρ) :
    crossedHeckeFun S σ c.val ∈ crossedCocycles ρ := by
  intro g h
  have key : ∀ j, σ (S.rep j)⁻¹ (c.val (S.delta (g * h) j)) =
      σ (S.rep j)⁻¹ (c.val (S.delta g j)) +
        ρ g (σ (S.rep (S.next g j))⁻¹ (c.val (S.delta h (S.next g j)))) := by
    intro j
    rw [S.delta_mul embedded, c.property, map_add, compat, ← Module.End.mul_apply, ← map_mul,
      S.rep_inv_delta, map_mul, Module.End.mul_apply, compat]
  rw [crossedHeckeFun_apply, Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    crossedHeckeFun_apply, crossedHeckeFun_apply, map_sum]
  congr 1
  exact Equiv.sum_comp (S.nextEquiv g) (fun k => ρ g (σ (S.rep k)⁻¹ (c.val (S.delta h k))))

/-- **The Hecke operator on crossed one-cocycles.** -/
def crossedHeckeCocycles : crossedCocycles ρ →ₗ[ℂ] crossedCocycles ρ where
  toFun c := ⟨crossedHeckeFun S σ c.val, crossedHeckeFun_mem S σ ρ compat embedded c⟩
  map_add' c d := by
    apply Subtype.ext
    funext g
    change crossedHeckeFun S σ (c.val + d.val) g =
      crossedHeckeFun S σ c.val g + crossedHeckeFun S σ d.val g
    simp only [crossedHeckeFun_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' a c := by
    apply Subtype.ext
    funext g
    change crossedHeckeFun S σ (a • c.val) g = a • crossedHeckeFun S σ c.val g
    simp only [crossedHeckeFun_apply, Pi.smul_apply, map_smul, Finset.smul_sum]

theorem crossedHeckeCocycles_apply (c : crossedCocycles ρ) (g : G) :
    (crossedHeckeCocycles S σ ρ compat embedded c).val g =
      ∑ j, σ (S.rep j)⁻¹ (c.val (S.delta g j)) := rfl

/-- The Hecke trace `∑_j σ(α_j)⁻¹ v` of a vector. -/
def traceVector (v : V) : V := ∑ j, σ (S.rep j)⁻¹ v

include compat in
theorem crossedHeckeCocycles_boundary (v : V) :
    crossedHeckeCocycles S σ ρ compat embedded (crossedBoundary ρ v) =
      crossedBoundary ρ (traceVector S σ v) := by
  apply Subtype.ext
  funext g
  change ∑ j, σ (S.rep j)⁻¹ (ρ (S.delta g j) v - v) = ρ g (traceVector S σ v) - traceVector S σ v
  have key : ∀ j, σ (S.rep j)⁻¹ (ρ (S.delta g j) v - v) =
      ρ g (σ (S.rep (S.next g j))⁻¹ v) - σ (S.rep j)⁻¹ v := by
    intro j
    rw [map_sub, compat, ← Module.End.mul_apply, ← map_mul, S.rep_inv_delta, map_mul,
      Module.End.mul_apply, compat]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_sub_distrib, traceVector, map_sum]
  congr 1
  exact Equiv.sum_comp (S.nextEquiv g) (fun k => ρ g (σ (S.rep k)⁻¹ v))

theorem crossedHeckeCocycles_boundaries :
    crossedBoundaries ρ ≤
      (crossedBoundaries ρ).comap (crossedHeckeCocycles S σ ρ compat embedded) := by
  rintro c ⟨v, rfl⟩
  exact ⟨traceVector S σ v, (crossedHeckeCocycles_boundary S σ ρ compat embedded v).symm⟩

/-- **The Hecke operator on `CrossedH1 ρ`.** -/
def crossedHecke : Module.End ℂ (CrossedH1 ρ) :=
  (crossedBoundaries ρ).mapQ (crossedBoundaries ρ) (crossedHeckeCocycles S σ ρ compat embedded)
    (crossedHeckeCocycles_boundaries S σ ρ compat embedded)

theorem crossedHecke_mk (c : crossedCocycles ρ) :
    crossedHecke S σ ρ compat embedded ((crossedBoundaries ρ).mkQ c) =
      (crossedBoundaries ρ).mkQ (crossedHeckeCocycles S σ ρ compat embedded c) := rfl

section Pullback

variable {H : Type} [Group H] (ι : H →* G) (S' : RightCosets (embed.comp ι))
  (e : S'.index ≃ S.index) (hrep : ∀ j, S'.rep j = S.rep (e j))
  (hdelta : ∀ h j, ι (S'.delta h j) = S.delta (ι h) (e j))

include hrep hdelta in
/-- **Restriction intertwines the Hecke operators** when the subgroup has the same
representatives and compatible transitions. -/
theorem pullback_crossedHecke (embedded' : Function.Injective (embed.comp ι)) (x : CrossedH1 ρ) :
    crossedPullbackH1 ι ρ (crossedHecke S σ ρ compat embedded x) =
      crossedHecke S' σ (ρ.comp ι) (fun h => compat (ι h)) embedded'
        (crossedPullbackH1 ι ρ x) := by
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [crossedHecke_mk, crossedPullbackH1_mk, crossedPullbackH1_mk, crossedHecke_mk]
  congr 1
  apply Subtype.ext
  funext h
  change ∑ j, σ (S.rep j)⁻¹ (c.val (S.delta (ι h) j)) =
    ∑ j, σ (S'.rep j)⁻¹ (c.val (ι (S'.delta h j)))
  simp only [hrep, hdelta]
  exact (Equiv.sum_comp e (fun k => σ (S.rep k)⁻¹ (c.val (S.delta (ι h) k)))).symm

end Pullback

section Primitive

variable {K X : Type} [Group K] [MulAction K X] (φ : 𝔾 →* K)

/-- The Hecke trace `∑_j σ(α_j)⁻¹ F(α_j x)` of a function on a `𝔾`-set. -/
def traceFunction (F : X → V) (x : X) : V :=
  ∑ j, σ (S.rep j)⁻¹ (F (φ (S.rep j) • x))

include compat in
/-- **Primitives.** If `F` is a primitive of `c` (`c(g) = F(g x) - ρ(g) F(x)`), the Hecke trace of
`F` is a primitive of `T c`. -/
theorem crossedHeckeFun_primitive (c : G → V) (F : X → V)
    (primitive : ∀ g x, c g = F (φ (embed g) • x) - ρ g (F x)) (g : G) (x : X) :
    crossedHeckeFun S σ c g = traceFunction S σ φ F (φ (embed g) • x) -
      ρ g (traceFunction S σ φ F x) := by
  have key : ∀ j, σ (S.rep j)⁻¹ (c (S.delta g j)) =
      σ (S.rep j)⁻¹ (F (φ (S.rep j) • φ (embed g) • x)) -
        ρ g (σ (S.rep (S.next g j))⁻¹ (F (φ (S.rep (S.next g j)) • x))) := by
    intro j
    have hpoint : φ (S.rep j) • φ (embed g) • x =
        φ (embed (S.delta g j)) • φ (S.rep (S.next g j)) • x := by
      rw [smul_smul, smul_smul, ← map_mul, ← map_mul, S.delta_spec, inv_mul_cancel_right]
    rw [primitive _ (φ (S.rep (S.next g j)) • x), hpoint, map_sub, compat,
      ← Module.End.mul_apply (σ (S.rep j)⁻¹), ← map_mul, S.rep_inv_delta, map_mul,
      Module.End.mul_apply, compat]
  rw [crossedHeckeFun_apply, Finset.sum_congr rfl (fun j _ => key j), Finset.sum_sub_distrib,
    traceFunction, traceFunction, map_sum]
  congr 1
  exact Equiv.sum_comp (S.nextEquiv g)
    (fun k => ρ g (σ (S.rep k)⁻¹ (F (φ (S.rep k) • x))))

end Primitive

end Generic

section LevelThree

variable (m : ℕ) (e : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- `Sym^m(ℂ²) ⊗ det^e` as a representation of `GL₂(ℚ)`. -/
abbrev rationalRho : Representation ℂ (GL (Fin 2) ℚ) (Binary.HomogeneousPoly m) :=
  (Binary.homogeneousAction m e).comp (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ))

theorem map_integralEmbed (g : GL (Fin 2) ℤ) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ) (integralEmbed g) = binaryIntegralComplex g := by
  apply Units.ext
  ext i j
  simp [integralEmbed, binaryIntegralComplex, Matrix.GeneralLinearGroup.map_apply]

theorem level_compat (g : binaryArithmeticLevel) :
    levelRep m e g = rationalRho m e (levelEmbed g) := by
  change Binary.homogeneousAction m e (binaryIntegralComplex g.val) =
    Binary.homogeneousAction m e
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ) (integralEmbed g.val))
  rw [map_integralEmbed]

theorem core_compat (k : core) : coreRep m e k = rationalRho m e (coreEmbed k) :=
  level_compat m e k

/-- **The Hecke operator `T_p` on `H¹(Γ₁'(3), Sym^m ⊗ det^e)`** (Sol's `CrossedH1` model):
`(T c)(g) = ∑_{j ∈ {0,…,p-1,∞}} σ(α_j)⁻¹ c(α_j g α_{next g j}⁻¹)`, `α_j = [[1, j], [0, p]]`,
`α_∞ = ε_p [[p, 0], [0, 1]]` (`ε_p = ±1 ≡ p mod 3`). -/
def levelHecke : Module.End ℂ (CrossedH1 (levelRep m e)) :=
  crossedHecke (levelCosets p hp3) (rationalRho m e) (levelRep m e) (level_compat m e)
    levelEmbed_injective

/-- **The Hecke operator `T_p` on `H¹(Γ₁(3), Sym^m ⊗ det^e)`**, same representatives and
transitions. -/
def coreHecke : Module.End ℂ (CrossedH1 (coreRep m e)) :=
  crossedHecke (coreCosets p hp3) (rationalRho m e) (coreRep m e) (core_compat m e)
    coreEmbed_injective

/-- The cocycle-level formula for `levelHecke`. -/
theorem levelHecke_mk (c : crossedCocycles (levelRep m e)) :
    levelHecke m e p hp3 (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk
        (crossedHeckeCocycles (levelCosets p hp3) (rationalRho m e) (levelRep m e)
          (level_compat m e) levelEmbed_injective c) := rfl

theorem levelHeckeCocycles_apply (c : crossedCocycles (levelRep m e)) (g : binaryArithmeticLevel) :
    (crossedHeckeCocycles (levelCosets p hp3) (rationalRho m e) (levelRep m e)
        (level_compat m e) levelEmbed_injective c).val g =
      ∑ j, rationalRho m e (heckeRep p j)⁻¹ (c.val (levelDelta p hp3 g j)) := rfl

/-- The cocycle-level formula for `coreHecke`. -/
theorem coreHecke_mk (c : crossedCocycles (coreRep m e)) :
    coreHecke m e p hp3 (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk
        (crossedHeckeCocycles (coreCosets p hp3) (rationalRho m e) (coreRep m e)
          (core_compat m e) coreEmbed_injective c) := rfl

/-- **Restriction `Γ₁'(3) → Γ₁(3)` intertwines the Hecke operators.** -/
theorem restriction_levelHecke (x : CrossedH1 (levelRep m e)) :
    restriction e m (levelHecke m e p hp3 x) = coreHecke m e p hp3 (restriction e m x) :=
  pullback_crossedHecke (levelCosets p hp3) (rationalRho m e) (levelRep m e) (level_compat m e)
    levelEmbed_injective core.subtype (coreCosets p hp3) (Equiv.refl _) (fun _ => rfl)
    (fun _ _ => rfl) coreEmbed_injective x

/-- The Hecke operator on the codomain `CrossedH1 (binaryArithmeticRepresentation n)` of
`BadLineLocal.badLineLeviMap` (coefficients `Sym^{n+1}`, twist `0`). -/
abbrev badLevelHecke (n : ℕ) : Module.End ℂ (CrossedH1 (binaryArithmeticRepresentation n)) :=
  levelHecke (n + 1) 0 p hp3

end LevelThree

end TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1
