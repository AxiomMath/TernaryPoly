module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.HeckeTp
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Parity

@[expose] public section


/-!
# Hecke equivariance of the parity-projected period map

For `m > 0` the parity-projected period map
`levelPeriodMap m e : S_{m+2}(Γ₁(3)) → H¹(Γ₁'(3), ρ_e)` intertwines the Hecke operator
`levelHecke m e p` on `H¹(Γ₁'(3), Sym^m ⊗ det^e)` with `p^{-e} T_p`:

**`levelHecke_levelPeriodMap`**:
`levelHecke m e p (levelPeriodMap m e f) = levelPeriodMap m e (p^{-e} T_p f)`.

The proof: restriction to `Γ₁(3)` is injective and
`restriction ∘ levelPeriodMap = π₊ ∘ levelThreePeriodMap`, where `π₊ [c] = [(c + ι c)/2]` is the
projection of `H¹(Γ₁(3))` onto the `ι`-invariant classes (`ι` = conjugation by `ε = diag(-1,1)`).
The Hecke operator `coreHecke` commutes with `π₊` (`coreHecke_plusH1`) because
`H¹(Γ₁(3)) = res H¹(Γ₁'(3), ρ_e) ⊕ tres H¹(Γ₁'(3), ρ_{e+1})`, `π₊` is the identity on the first
summand and zero on the second, and `coreHecke` preserves both summands
(`restriction_levelHecke`, `coreHecke_tres`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix UpperHalfPlane
open scoped Manifold ModularForm MatrixGroups
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.LevelThree.TwistSplitting
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodHeckeTp
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
open TernaryPeriodPolynomials.LevelThree.LevelThreeHecke

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParityHecke

/-! ### The projection `π₊` on the first cohomology of an index-two subgroup -/

section Generic

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {H : Subgroup G} {ε : G}
  (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)

include hεε in
/-- `ρ(ε) z(ε k ε) = z(k) + (ρ(k) - 1) z(ε)` for a cocycle `z` of `G`. -/
theorem conj_pullback (ρ : Representation ℂ G V) (z : crossedCocycles ρ) (k : G) :
    ρ ε (z.val (ε * k * ε)) = z.val k + (ρ k (z.val ε) - z.val ε) := by
  have h1 : z.val (ε * k * ε) = z.val ε + ρ ε (z.val k + ρ k (z.val ε)) := by
    rw [mul_assoc, cocycle_mul, cocycle_mul]
  have h2 : z.val ε + ρ ε (z.val ε) = 0 := by
    have h := cocycle_mul z ε ε
    rw [hεε, cocycle_one] at h
    exact h.symm
  have h3 : ρ ε (ρ ε (z.val k + ρ k (z.val ε))) = z.val k + ρ k (z.val ε) :=
    rho_eps_eps ρ hεε _
  have h4 : ρ ε (z.val ε) = -z.val ε :=
    eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h2)
  rw [h1, map_add, h3, h4]
  abel

theorem plusLin_boundary (ρ : Representation ℂ G V) (v : V) :
    plusLin ρ hεε normal (crossedBoundary (ρ.comp H.subtype) v) =
      crossedBoundary (ρ.comp H.subtype) ((2 : ℂ)⁻¹ • (v + ρ ε v)) := by
  apply Subtype.ext
  funext k
  have h := rho_conj hεε normal ρ k v
  change (2 : ℂ)⁻¹ • ((ρ k.val v - v) + ρ ε (ρ (ε * k.val * ε) v - v)) =
    ρ k.val ((2 : ℂ)⁻¹ • (v + ρ ε v)) - (2 : ℂ)⁻¹ • (v + ρ ε v)
  change ρ ε (ρ (ε * k.val * ε) v) = ρ k.val (ρ ε v) at h
  rw [map_sub, h, map_smul, map_add]
  module

/-- The projection `π₊ [z] = [(z + ι z)/2]` on `H¹(H, ρ)`. -/
def plusMap (ρ : Representation ℂ G V) :
    CrossedH1 (ρ.comp H.subtype) →ₗ[ℂ] CrossedH1 (ρ.comp H.subtype) :=
  (crossedBoundaries (ρ.comp H.subtype)).mapQ (crossedBoundaries (ρ.comp H.subtype))
    (plusLin ρ hεε normal) (by
      rintro _ ⟨v, rfl⟩
      exact ⟨(2 : ℂ)⁻¹ • (v + ρ ε v), (plusLin_boundary hεε normal ρ v).symm⟩)

theorem plusMap_mk (ρ : Representation ℂ G V) (z : crossedCocycles (ρ.comp H.subtype)) :
    plusMap hεε normal ρ (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (plusLin ρ hεε normal z) :=
  rfl

/-- `π₊` is the identity on classes restricted from `G`. -/
theorem plusMap_pullback (ρ : Representation ℂ G V) (z : crossedCocycles ρ) :
    plusMap hεε normal ρ (crossedPullbackH1 H.subtype ρ (Submodule.Quotient.mk z)) =
      crossedPullbackH1 H.subtype ρ (Submodule.Quotient.mk z) := by
  have h : crossedPullbackH1 H.subtype ρ (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (crossedPullbackCocycles H.subtype ρ z) := rfl
  rw [h, plusMap_mk, Submodule.Quotient.eq]
  refine ⟨(2 : ℂ)⁻¹ • z.val ε, ?_⟩
  apply Subtype.ext
  funext k
  have hc := conj_pullback hεε ρ z k.val
  change ρ k.val ((2 : ℂ)⁻¹ • z.val ε) - (2 : ℂ)⁻¹ • z.val ε =
    (2 : ℂ)⁻¹ • (z.val k.val + ρ ε (z.val (ε * k.val * ε))) - z.val k.val
  rw [hc, map_smul]
  module

/-- `π₊` kills classes restricted from the other twist. -/
theorem plusMap_twisted (ρ ρ₂ : Representation ℂ G V) (agree : ∀ k : H, ρ₂ k.val = ρ k.val)
    (anti : ρ₂ ε = -(ρ ε)) (z : crossedCocycles ρ₂) :
    plusMap hεε normal ρ
      (twistedRestrictionH1 ρ ρ₂ agree (Submodule.Quotient.mk z)) = 0 := by
  have h : twistedRestrictionH1 ρ ρ₂ agree (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (twistedRestriction ρ ρ₂ agree z) := rfl
  rw [h, plusMap_mk, Submodule.Quotient.mk_eq_zero]
  refine ⟨(-(2 : ℂ)⁻¹) • z.val ε, ?_⟩
  apply Subtype.ext
  funext k
  have hc := conj_pullback hεε ρ₂ z k.val
  have hanti : ∀ w : V, ρ ε w = -ρ₂ ε w := by
    intro w
    rw [anti]
    simp
  have hk := agree k
  change ρ k.val ((-(2 : ℂ)⁻¹) • z.val ε) - (-(2 : ℂ)⁻¹) • z.val ε =
    (2 : ℂ)⁻¹ • (z.val k.val + ρ ε (z.val (ε * k.val * ε)))
  rw [hanti, hc, hk, map_smul]
  module

end Generic

/-! ### `π₊` and the Hecke operator at level three -/

section Level

variable {m : ℕ} (e : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- The normality condition for `Γ₁(3) ⊴ Γ₁'(3)`. -/
theorem normalCore : ∀ k ∈ core, reflection * k * reflection ∈ core :=
  fun _ hk => conj_mem_core hk

/-- `π₊` on `H¹(Γ₁(3), Sym^m ⊗ det^e)`. -/
abbrev plusH1 (m : ℕ) (e : ℤ) : CrossedH1 (coreRep m e) →ₗ[ℂ] CrossedH1 (coreRep m e) :=
  plusMap (H := core) (ε := reflection) reflection_mul_self normalCore (levelRep m e)

/-- Restriction from the other twist. -/
abbrev tres (m : ℕ) (e : ℤ) : CrossedH1 (levelRep m (e + 1)) →ₗ[ℂ] CrossedH1 (coreRep m e) :=
  twistedRestrictionH1 (H := core) (levelRep m e) (levelRep m (e + 1))
    (ExactLevel.twist_agree m e)

theorem plusH1_restriction (x : CrossedH1 (levelRep m e)) :
    plusH1 m e (restriction e m x) = restriction e m x := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  exact plusMap_pullback (H := core) (ε := reflection) reflection_mul_self normalCore
    (levelRep m e) z

theorem plusH1_tres (y : CrossedH1 (levelRep m (e + 1))) : plusH1 m e (tres m e y) = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
  exact plusMap_twisted (H := core) (ε := reflection) reflection_mul_self normalCore
    (levelRep m e) (levelRep m (e + 1)) (ExactLevel.twist_agree m e) (ExactLevel.twist_anti m e) z

/-- Raising the twist multiplies by the determinant. -/
theorem homogeneousAction_succ (m : ℕ) (e : ℤ) (g : Binary.GL2) :
    Binary.homogeneousAction m (e + 1) g =
      ((GeneralLinearGroup.det g : ℂˣ) : ℂ) • Binary.homogeneousAction m e g := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [LinearMap.smul_apply, Submodule.coe_smul, Binary.homogeneousAction_coe,
    Binary.homogeneousAction_coe, Binary.action_apply, Binary.action_apply, smul_smul]
  congr 1
  change ((GeneralLinearGroup.det g : ℂˣ) : ℂ) ^ (e + 1) =
    ((GeneralLinearGroup.det g : ℂˣ) : ℂ) * ((GeneralLinearGroup.det g : ℂˣ) : ℂ) ^ e
  rw [zpow_add_one₀ (Units.ne_zero _), mul_comm]

/-- The scalar relating the Hecke matrices of consecutive twists. -/
theorem rationalRho_succ_inv (j : Option (Fin p.val)) (w : Binary.HomogeneousPoly m) :
    rationalRho m (e + 1) (heckeRep p j)⁻¹ w =
      ((p.val : ℂ)⁻¹) • rationalRho m e (heckeRep p j)⁻¹ w := by
  have h1 : (((heckeRep p j)⁻¹).val.det : ℚ) = (p.val : ℚ)⁻¹ := by
    rw [← GeneralLinearGroup.val_det_apply, map_inv, Units.val_inv_eq_inv_val,
      GeneralLinearGroup.val_det_apply, heckeRep_det]
  have h2 : ((GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℂ) (heckeRep p j)⁻¹) : ℂˣ) : ℂ) = (p.val : ℂ)⁻¹ := by
    rw [GeneralLinearGroup.val_det_apply]
    have h := RingHom.map_det (algebraMap ℚ ℂ) ((heckeRep p j)⁻¹).val
    rw [RingHom.mapMatrix_apply] at h
    change (((heckeRep p j)⁻¹).val.map (algebraMap ℚ ℂ)).det = _
    rw [← h, h1]
    simp
  change Binary.homogeneousAction m (e + 1)
      (GeneralLinearGroup.map (algebraMap ℚ ℂ) (heckeRep p j)⁻¹) w =
    (p.val : ℂ)⁻¹ • Binary.homogeneousAction m e
      (GeneralLinearGroup.map (algebraMap ℚ ℂ) (heckeRep p j)⁻¹) w
  rw [homogeneousAction_succ, LinearMap.smul_apply, h2]

theorem tres_mk (z : crossedCocycles (levelRep m (e + 1))) :
    tres m e (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (twistedRestriction (H := core) (levelRep m e)
        (levelRep m (e + 1)) (ExactLevel.twist_agree m e) z) := rfl

/-- `coreHecke` preserves the image of the other twist (up to the scalar `p`). -/
theorem coreHecke_tres (y : CrossedH1 (levelRep m (e + 1))) :
    coreHecke m e p hp3 (tres m e y) =
      (p.val : ℂ) • tres m e (levelHecke m (e + 1) p hp3 y) := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
  have hz : (crossedBoundaries (levelRep m (e + 1))).mkQ z = Submodule.Quotient.mk z := rfl
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  rw [hz, tres_mk, coreHecke_mk, levelHecke_mk, tres_mk, ← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  funext k
  change ∑ j, rationalRho m e (heckeRep p j)⁻¹ (z.val (levelDelta p hp3 k.val j)) =
    (p.val : ℂ) • ∑ j, rationalRho m (e + 1) (heckeRep p j)⁻¹ (z.val (levelDelta p hp3 k.val j))
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [rationalRho_succ_inv e p j, smul_smul, mul_inv_cancel₀ hp, one_smul]

theorem coreHecke_restriction (a : CrossedH1 (levelRep m e)) :
    coreHecke m e p hp3 (restriction e m a) = restriction e m (levelHecke m e p hp3 a) :=
  (restriction_levelHecke m e p hp3 a).symm

/-- **`coreHecke` commutes with the projection `π₊`.** -/
theorem coreHecke_plusH1 (x : CrossedH1 (coreRep m e)) :
    coreHecke m e p hp3 (plusH1 m e x) = plusH1 m e (coreHecke m e p hp3 x) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := splitMap_surjective (H := core) (ε := reflection) (levelRep m e)
    (levelRep m (e + 1)) mem_core_or reflection_mul_self normalCore (ExactLevel.twist_agree m e)
    (ExactLevel.twist_anti m e) x
  have hsplit : splitMap (levelRep m e) (levelRep m (e + 1)) (ExactLevel.twist_agree m e) (a, b) =
      restriction e m a + tres m e b := rfl
  rw [hsplit]
  simp only [map_add, map_smul, coreHecke_restriction, coreHecke_tres, plusH1_restriction,
    plusH1_tres, smul_zero, add_zero]

/-- The restriction of the parity-projected period class is `π₊` of the period class. -/
theorem res_levelPeriodMap (f : S m) :
    restriction e m (levelPeriodMap m e f) = plusH1 m e (levelThreePeriodMap m e f) := by
  have h1 : restriction e m (levelPeriodMap m e f) = Submodule.Quotient.mk
      (crossedPullbackCocycles core.subtype (levelRep m e)
        (levelPlus m e (periodCocycle m e f))) := rfl
  have h2 : plusH1 m e (levelThreePeriodMap m e f) = Submodule.Quotient.mk
      (plusLin (levelRep m e) reflection_mul_self normalCore (periodCocycle m e f)) := rfl
  rw [h1, h2]
  congr 1
  apply Subtype.ext
  funext k
  exact levelPlus_core m e (periodCocycle m e f) k

/-- **Hecke equivariance of the parity-projected period map.** -/
theorem levelHecke_levelPeriodMap (hm : 0 < m) (f : S m) :
    levelHecke m e p hp3 (levelPeriodMap m e f) =
      levelPeriodMap m e (((p.val : ℂ) ^ (-e)) • levelThreeHecke ((m : ℤ) + 2) p hp3 f) := by
  apply restriction_injective e hm
  rw [restriction_levelHecke, res_levelPeriodMap, res_levelPeriodMap,
    ← periodMap_hecke_tp p hp3 e f]
  exact coreHecke_plusH1 e p hp3 _

end Level

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParityHecke
