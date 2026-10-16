module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Parity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.PolynomialParity

@[expose] public section


/-!
# Vanishing of the parity-projected period class forces interior coordinates to vanish

Let `z` be a crossed cocycle of `Γ₁(3) = ⟨T, L⟩` with values in `Sym^m ⊗ det^e` and boundary
values `z(T) = a - T a`, `z(L) = b - L b`. If the extension to `Γ₁'(3) = Γ₁(3) ⊔ Γ₁(3) ε` of its
symmetric part `(z + ι z)/2` is a coboundary (`v ↦ g v - v`), then evaluating at `T` and `L`,
using `ε T ε = T⁻¹` and `ε L ε = L⁻¹`, shows that `a⁺ + v` is fixed by `T` and `b⁺ + v` is fixed by
`L`, where `x⁺ = (x + ε x)/2` (`fixed_of_plus_boundary`). The fixed lines are spanned by `X₁^m` and
`X₀^m`, so every interior coordinate of `a⁺ - b⁺` vanishes. Since `ε` acts on the monomial
`X₀^j X₁^(m-j)` by `(-1)^(e+j)` (`coord_reflection`), for `e + j` even this is the `j`-th coordinate
of `a - b` (`coord_eq_zero_of_plus_boundary`, `coord_eq_zero_of_levelPeriodMap_eq_zero`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix MvPolynomial Module
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.LevelThree.TwistSplitting
open TernaryPeriodPolynomials.LevelThree.SymFixed
open TernaryPeriodPolynomials.LevelThree.SharpBounds
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity

namespace TernaryPeriodPolynomials.LevelThreeInjective.ParityCriterion

/-! ### The symmetric part of a boundary value -/

section Generic

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- If `z(t) = a - t a` and `(z(t) + ε z(ε t ε))/2 = t v - v` with `ε t ε = t⁻¹`, then
`(a + ε a)/2 + v` is fixed by `t`. -/
theorem fixed_of_plus_boundary {t ε : G} (hεε : ε * ε = 1) (hεt : ε * t * ε = t⁻¹) (a v : V)
    (h : (2 : ℂ)⁻¹ • ((a - ρ t a) + ρ ε (-(ρ t⁻¹ (a - ρ t a)))) = ρ t v - v) :
    ρ t ((2 : ℂ)⁻¹ • (a + ρ ε a) + v) = (2 : ℂ)⁻¹ • (a + ρ ε a) + v := by
  have key : ε * t⁻¹ = t * ε := by
    rw [← hεt, ← mul_assoc, ← mul_assoc, hεε, one_mul]
  have hop : ρ ε (ρ t⁻¹ a) = ρ t (ρ ε a) := by
    rw [← Module.End.mul_apply, ← map_mul, key, map_mul, Module.End.mul_apply]
  have hcancel : ρ t⁻¹ (ρ t a) = a := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have h2 : ρ ε (-(ρ t⁻¹ (a - ρ t a))) = ρ ε a - ρ t (ρ ε a) := by
    rw [map_sub, hcancel, neg_sub, map_sub, hop]
  rw [h2] at h
  have hv : ρ t v = (2 : ℂ)⁻¹ • ((a - ρ t a) + (ρ ε a - ρ t (ρ ε a))) + v := by
    rw [h]
    abel
  rw [map_add, map_smul, map_add, hv]
  module

end Generic

/-! ### The reflection and the endpoint lines in the monomial basis -/

section Basis

variable (m : ℕ) (e : ℤ)

/-- `ε = diag(-1, 1)` acts on `X₀^i X₁^(m-i)` by `(-1)^(e+i)`. -/
theorem reflection_basis (i : Fin (m + 1)) :
    Binary.homogeneousAction m e reflectionC (binaryStandardBasis m i) =
      ((-1 : ℂ) ^ (e + (i.val : ℤ))) • binaryStandardBasis m i := by
  apply Subtype.ext
  apply MvPolynomial.funext
  intro x
  rw [Binary.homogeneousAction_coe, eval_vec, eval_reflection, Submodule.coe_smul,
    MvPolynomial.smul_eval, eval_vec _ x, binaryStandardBasis_coe]
  simp only [map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [zpow_add₀ (neg_ne_zero.mpr one_ne_zero), zpow_natCast, neg_pow]
  ring

/-- The `j`-th coordinate of `ε x` is `(-1)^(e+j)` times that of `x`. -/
theorem coord_reflection (x : Binary.HomogeneousPoly m) (j : Fin (m + 1)) :
    (binaryStandardBasis m).coord j (Binary.homogeneousAction m e reflectionC x) =
      (-1 : ℂ) ^ (e + (j.val : ℤ)) * (binaryStandardBasis m).coord j x := by
  have hlin : (binaryStandardBasis m).coord j ∘ₗ Binary.homogeneousAction m e reflectionC =
      ((-1 : ℂ) ^ (e + (j.val : ℤ))) • (binaryStandardBasis m).coord j := by
    apply (binaryStandardBasis m).ext
    intro i
    simp only [LinearMap.comp_apply, reflection_basis, map_smul, LinearMap.smul_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul, Finsupp.single_apply]
    split_ifs with hij
    · subst hij
      rfl
    · rw [mul_zero, mul_zero]
  exact LinearMap.congr_fun hlin x

theorem basis_zero_eq : binaryStandardBasis m 0 = powerVector 1 m := by
  apply Subtype.ext
  rw [binaryStandardBasis_coe]
  simp [powerVector]

theorem basis_last_eq : binaryStandardBasis m (Fin.last m) = powerVector 0 m := by
  apply Subtype.ext
  rw [binaryStandardBasis_coe]
  simp [powerVector]

theorem mem_span_of_finrank_one {W : Submodule ℂ (Binary.HomogeneousPoly m)}
    (h : finrank ℂ W = 1) {u : Binary.HomogeneousPoly m} (hu : u ∈ W) (hu0 : u ≠ 0)
    {x : Binary.HomogeneousPoly m} (hx : x ∈ W) : x ∈ (ℂ ∙ u) := by
  have hne : (⟨u, hu⟩ : W) ≠ 0 := fun h0 => hu0 (congrArg Subtype.val h0)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨u, hu⟩ : W) hne).mp h ⟨x, hx⟩
  exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩

/-- A `T`-fixed vector lies on the line `ℂ X₁^m`, inside the endpoint span. -/
theorem mem_endpoint_of_fixed_upper {x : Binary.HomogeneousPoly m}
    (hx : x ∈ fixedSpace e (upperC 1)) : x ∈ binaryEndpointPolynomialSpan m := by
  have hmem : binaryStandardBasis m 0 ∈ fixedSpace (m := m) e (upperC 1) := by
    rw [basis_zero_eq]
    exact powerVector_one_mem_upper e 1
  have hline := mem_span_of_finrank_one m (finrank_fixed_upper (m := m) e one_ne_zero) hmem
    ((binaryStandardBasis m).ne_zero 0) hx
  exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) hline

/-- An `L`-fixed vector lies on the line `ℂ X₀^m`, inside the endpoint span. -/
theorem mem_endpoint_of_fixed_lower {x : Binary.HomogeneousPoly m}
    (hx : x ∈ fixedSpace e (lowerC 3)) : x ∈ binaryEndpointPolynomialSpan m := by
  have hmem : binaryStandardBasis m (Fin.last m) ∈ fixedSpace (m := m) e (lowerC 3) := by
    rw [basis_last_eq]
    exact powerVector_zero_mem_lower e 3
  have hline := mem_span_of_finrank_one m
    (finrank_fixed_lower (m := m) e (by norm_num : (3 : ℂ) ≠ 0)) hmem
    ((binaryStandardBasis m).ne_zero (Fin.last m)) hx
  exact Submodule.span_mono
    (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hline

end Basis

/-! ### The criterion -/

section Criterion

variable {m : ℕ} {e : ℤ}

/-- The extended symmetric part at an element `k` of `Γ₁(3)` inverted by `ε`. -/
theorem plus_value (z : crossedCocycles (coreRep m e)) (k : core)
    (hk : reflection * k.val * reflection = k.val⁻¹) :
    (levelPlus m e z).val k.val =
      (2 : ℂ)⁻¹ • (z.val k + levelRep m e reflection (-(levelRep m e k.val⁻¹ (z.val k)))) := by
  rw [levelPlus_core]
  have hc : conjH (fun _ hk => conj_mem_core hk) k = k⁻¹ := Subtype.ext hk
  have hinv : z.val k⁻¹ = -(levelRep m e k.val⁻¹ (z.val k)) := cocycle_inv z k
  change (2 : ℂ)⁻¹ • (z.val k + levelRep m e reflection
    (z.val (conjH (fun _ hk => conj_mem_core hk) k))) = _
  rw [hc, hinv]

/-- **The parity criterion.** If the extended symmetric part of `z` is a coboundary, then every
interior coordinate `j` of `a - b` with `e + j` even vanishes. -/
theorem coord_eq_zero_of_plus_boundary (z : crossedCocycles (coreRep m e))
    (a b : Binary.HomogeneousPoly m)
    (hT : z.val coreT = a - coreRep m e coreT a) (hL : z.val coreL = b - coreRep m e coreL b)
    (h0 : levelPlus m e z ∈ crossedBoundaries (levelRep m e))
    (j : Fin (m + 1)) (hj0 : j ≠ 0) (hjm : j ≠ Fin.last m) (hpar : Even (e + (j.val : ℤ))) :
    (binaryStandardBasis m).coord j (a - b) = 0 := by
  obtain ⟨v, hv⟩ := h0
  have hval : ∀ g : binaryArithmeticLevel, (levelPlus m e z).val g = levelRep m e g v - v := by
    intro g
    rw [← hv]
    rfl
  have hTplus := plus_value z coreT hεT
  rw [hval, hT] at hTplus
  have hLplus := plus_value z coreL hεL
  rw [hval, hL] at hLplus
  have fixT := fixed_of_plus_boundary (levelRep m e) (t := upper 1) reflection_mul_self hεT a v
    hTplus.symm
  have fixL := fixed_of_plus_boundary (levelRep m e) (t := lower 1) reflection_mul_self hεL b v
    hLplus.symm
  rw [levelRep_T] at fixT
  rw [levelRep_L] at fixL
  have hA := mem_endpoint_of_fixed_upper m e ((mem_fixedSpace e).mpr fixT)
  have hB := mem_endpoint_of_fixed_lower m e ((mem_fixedSpace e).mpr fixL)
  have hdiff := Submodule.sub_mem _ hA hB
  rw [add_sub_add_right_eq_sub] at hdiff
  have hcoord := binaryEndpointPolynomialSpan_coord_zero m _ hdiff j hj0 hjm
  have hexp : (2 : ℂ)⁻¹ • (a + levelRep m e reflection a) -
      (2 : ℂ)⁻¹ • (b + levelRep m e reflection b) =
        (2 : ℂ)⁻¹ • ((a - b) + levelRep m e reflection (a - b)) := by
    rw [map_sub]
    module
  rw [hexp, map_smul, map_add, levelRep_ε, coord_reflection, hpar.neg_one_zpow, one_mul,
    smul_eq_mul] at hcoord
  have htwo : (2 : ℂ)⁻¹ * ((binaryStandardBasis m).coord j (a - b) +
      (binaryStandardBasis m).coord j (a - b)) = (binaryStandardBasis m).coord j (a - b) := by
    ring
  rw [htwo] at hcoord
  exact hcoord

/-- **The parity criterion for the period map.** -/
theorem coord_eq_zero_of_levelPeriodMap_eq_zero (f : S m) (a b : Binary.HomogeneousPoly m)
    (hT : (periodCocycle m e f).val coreT = a - coreRep m e coreT a)
    (hL : (periodCocycle m e f).val coreL = b - coreRep m e coreL b)
    (h0 : levelPeriodMap m e f = 0)
    (j : Fin (m + 1)) (hj0 : j ≠ 0) (hjm : j ≠ Fin.last m) (hpar : Even (e + (j.val : ℤ))) :
    (binaryStandardBasis m).coord j (a - b) = 0 := by
  rw [levelPeriodMap_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  exact coord_eq_zero_of_plus_boundary (periodCocycle m e f) a b hT hL h0 j hj0 hjm hpar

end Criterion

end TernaryPeriodPolynomials.LevelThreeInjective.ParityCriterion
