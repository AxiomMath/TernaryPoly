module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.FreeProduct
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ParabolicBounds

@[expose] public section


/-!
# Existence of cocycles on `Γ₁(3)` and the exact dimensions

Because `Γ₁(3) ≅ ℤ * ℤ/3` (`FreeProduct.coreEquiv`), a crossed homomorphism on `Γ₁(3)` can be
prescribed freely at `T` and, subject to `(1 + E + E²) b = 0`, at `E`
(`exists_cocycle`): the splitting `Γ₁(3) → V ⋊ Γ₁(3)` is the free-product lift of
`T ↦ (a, T)` and of the coboundary splitting on `⟨E⟩` (`H¹(ℤ/3, V) = 0`). Hence the bounds of
`TwoGenerator` / `ParabolicBounds` are equalities:

* `finrank_H1_core_eq`: `dim H¹(Γ₁(3), V) = dim V - dim V^E + dim V^{Γ₁(3)}` (any finite-dim `V`);
* **`finrank_core_H1_sym_eq`**: `dim H¹(Γ₁(3), Sym^m ⊗ det^e) = 2⌊(m + 2)/3⌋` for `m > 0`;
* `finrank_parabolicH1_core_eq`: `dim H¹_par = dim V - dim V^T - dim V^L - dim V^E` (no invariants,
  no coinvariants);
* **`finrank_core_parabolicH1_sym_eq`**: `dim H¹_par(Γ₁(3), Sym^m ⊗ det^e) = 2(⌊(m + 2)/3⌋ - 1)`,
  the Eichler–Shimura value `2 dim S_{m+2}(Γ₁(3))`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.Existence

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers GammaOneThree FreeProduct TwoGenerator
open Module Monoid

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ core V)

/-- `ρ` as automorphisms of `Multiplicative V`. -/
def actionAut : core →* MulAut (Multiplicative V) where
  toFun g := AddEquiv.toMultiplicative
    (Spectral.ModularSymDimension.actionEquiv ρ g).toAddEquiv
  map_one' := by
    ext x
    change Multiplicative.ofAdd (ρ 1 (Multiplicative.toAdd x)) = x
    rw [map_one, Module.End.one_apply]
    rfl
  map_mul' g h := by
    ext x
    change Multiplicative.ofAdd (ρ (g * h) (Multiplicative.toAdd x)) =
      Multiplicative.ofAdd (ρ g (ρ h (Multiplicative.toAdd x)))
    rw [map_mul, Module.End.mul_apply]

theorem actionAut_apply (g : core) (x : V) :
    actionAut ρ g (Multiplicative.ofAdd x) = Multiplicative.ofAdd (ρ g x) := rfl

/-- The split extension `V ⋊ Γ₁(3)`. -/
abbrev Extension := Multiplicative V ⋊[actionAut ρ] core

/-- The coboundary splitting `g ↦ (g w - w, g)`. -/
def coboundaryHom (w : V) : core →* Extension ρ where
  toFun g := ⟨Multiplicative.ofAdd (ρ g w - w), g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (ρ 1 w - w) = 1
      rw [map_one, Module.End.one_apply, sub_self]
      rfl
    · rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.mul_left]
      change Multiplicative.ofAdd (ρ (g * h) w - w) =
        Multiplicative.ofAdd (ρ g w - w) * Multiplicative.ofAdd (ρ g (ρ h w - w))
      rw [← ofAdd_add]
      congr 1
      rw [map_mul, Module.End.mul_apply, LinearMap.map_sub]
      abel
    · rfl

/-- The free-product data: `T ↦ (a, T)` and the coboundary splitting on `⟨E⟩`. -/
def liftFamily (a w : V) : (b : Bool) → Factor b →* Extension ρ
  | false => zpowersHom (Extension ρ) ⟨Multiplicative.ofAdd a, coreT⟩
  | true => (coboundaryHom ρ w).comp (Subgroup.zpowers coreE).subtype

/-- The splitting of `V ⋊ Γ₁(3) → Γ₁(3)` with prescribed values. -/
def splitting (a w : V) : core →* Extension ρ :=
  (CoprodI.lift (liftFamily ρ a w)).comp coreEquiv.symm.toMonoidHom

theorem coreEquiv_symm_T : coreEquiv.symm coreT = CoprodI.of (i := false) (Multiplicative.ofAdd 1) := by
  rw [MulEquiv.symm_apply_eq]
  change coreT = CoprodI.lift factorHom (CoprodI.of (i := false) (Multiplicative.ofAdd 1))
  rw [CoprodI.lift_of]
  change coreT = zpowersHom core coreT (Multiplicative.ofAdd 1)
  rw [zpowersHom_apply, toAdd_ofAdd, zpow_one]

theorem coreEquiv_symm_E :
    coreEquiv.symm coreE = CoprodI.of (i := true) ⟨coreE, Subgroup.mem_zpowers coreE⟩ := by
  rw [MulEquiv.symm_apply_eq]
  change coreE = CoprodI.lift factorHom (CoprodI.of (i := true) ⟨coreE, Subgroup.mem_zpowers coreE⟩)
  rw [CoprodI.lift_of]
  rfl

theorem splitting_T (a w : V) :
    splitting ρ a w coreT = ⟨Multiplicative.ofAdd a, coreT⟩ := by
  change CoprodI.lift (liftFamily ρ a w) (coreEquiv.symm coreT) = _
  rw [coreEquiv_symm_T, CoprodI.lift_of]
  change zpowersHom (Extension ρ) _ (Multiplicative.ofAdd 1) = _
  rw [zpowersHom_apply, toAdd_ofAdd, zpow_one]

theorem splitting_E (a w : V) :
    splitting ρ a w coreE = ⟨Multiplicative.ofAdd (ρ coreE w - w), coreE⟩ := by
  change CoprodI.lift (liftFamily ρ a w) (coreEquiv.symm coreE) = _
  rw [coreEquiv_symm_E, CoprodI.lift_of]
  rfl

theorem closure_T_E : Subgroup.closure ({coreT, coreE} : Set core) = ⊤ := by
  rw [eq_top_iff, ← core_closure, Subgroup.closure_le]
  have hT : coreT ∈ Subgroup.closure ({coreT, coreE} : Set core) := Subgroup.subset_closure (by simp)
  have hE : coreE ∈ Subgroup.closure ({coreT, coreE} : Set core) := Subgroup.subset_closure (by simp)
  rintro x (rfl | rfl)
  · exact hT
  · rw [coreL_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hE) hT

theorem splitting_right (a w : V) (g : core) : (splitting ρ a w g).right = g := by
  have key : (SemidirectProduct.rightHom).comp (splitting ρ a w) = MonoidHom.id core := by
    apply MonoidHom.eq_of_eqOn_dense closure_T_E
    rintro x (rfl | rfl)
    · change (splitting ρ a w coreT).right = coreT
      rw [splitting_T]
    · change (splitting ρ a w coreE).right = coreE
      rw [splitting_E]
  exact congrArg (fun f : core →* core => f g) key

/-- The crossed homomorphism of the splitting. -/
def splittingCocycle (a w : V) : crossedCocycles ρ :=
  ⟨fun g => Multiplicative.toAdd (splitting ρ a w g).left, by
    intro g h
    have product := congrArg SemidirectProduct.left ((splitting ρ a w).map_mul g h)
    rw [SemidirectProduct.mul_left, splitting_right] at product
    change Multiplicative.toAdd (splitting ρ a w (g * h)).left =
      Multiplicative.toAdd (splitting ρ a w g).left + ρ g (Multiplicative.toAdd (splitting ρ a w h).left)
    rw [product, toAdd_mul]
    rfl⟩

theorem splittingCocycle_T (a w : V) : (splittingCocycle ρ a w).val coreT = a := by
  change Multiplicative.toAdd (splitting ρ a w coreT).left = a
  rw [splitting_T]
  rfl

theorem splittingCocycle_E (a w : V) : (splittingCocycle ρ a w).val coreE = ρ coreE w - w := by
  change Multiplicative.toAdd (splitting ρ a w coreE).left = _
  rw [splitting_E]
  rfl

/-- **Existence**: values at `T` and `E` can be prescribed, subject to `N_E b = 0`. -/
theorem exists_cocycle (a b : V) (hb : norm3 ρ coreE b = 0) :
    ∃ z : crossedCocycles ρ, z.val coreT = a ∧ z.val coreE = b := by
  let w : V := (3 : ℂ)⁻¹ • (ρ coreE b + (2 : ℂ) • ρ coreE (ρ coreE b))
  refine ⟨splittingCocycle ρ a w, splittingCocycle_T ρ a w, ?_⟩
  rw [splittingCocycle_E]
  have h3 : ρ coreE (ρ coreE (ρ coreE b)) = b := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      show coreE * coreE * coreE = coreE ^ 3 by rw [pow_succ, pow_two], coreE_cube, map_one,
      Module.End.one_apply]
  rw [norm3_apply] at hb
  simp only [w, map_smul, map_add, h3]
  linear_combination (norm := module) (-(3 : ℂ)⁻¹) • hb

section Exact

variable [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem coreE_cube_apply (v : V) : ρ coreE (ρ coreE (ρ coreE v)) = v := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    show coreE * coreE * coreE = coreE ^ 3 by rw [pow_succ, pow_two], coreE_cube, map_one,
    Module.End.one_apply]

omit [FiniteDimensional ℂ V] in
theorem range_norm3_eq : LinearMap.range (norm3 ρ coreE) = fixed ρ coreE := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [mem_fixed, norm3_apply, map_add, map_add, coreE_cube_apply]
    abel
  · exact fixed_le_range_norm3 coreE

theorem finrank_ker_norm3 :
    finrank ℂ (LinearMap.ker (norm3 ρ coreE)) + finrank ℂ (fixed ρ coreE) = finrank ℂ V := by
  have := LinearMap.finrank_range_add_finrank_ker (norm3 ρ coreE)
  rw [range_norm3_eq] at this
  omega

omit [FiniteDimensional ℂ V] in
theorem pairMap_surjective : Function.Surjective (pairMap (ρ := ρ) core_elliptic_cube) := by
  rintro ⟨a, ⟨b, hb⟩⟩
  obtain ⟨z, hT, hE⟩ := exists_cocycle ρ a b hb
  refine ⟨z, ?_⟩
  apply Prod.ext
  · exact hT
  · exact Subtype.ext hE

theorem finrank_cocycles_core :
    finrank ℂ (crossedCocycles ρ) = finrank ℂ V + finrank ℂ (LinearMap.ker (norm3 ρ coreE)) := by
  rw [(LinearEquiv.ofBijective _ ⟨pairMap_injective (ρ := ρ) core_closure core_elliptic_cube,
    pairMap_surjective ρ⟩).finrank_eq, Module.finrank_prod]

omit [FiniteDimensional ℂ V] in
theorem ker_boundary_core : LinearMap.ker (crossedBoundary ρ) = fixed ρ coreT ⊓ fixed ρ coreL := by
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker, boundary_eq_zero_iff] at hv
    exact ⟨(mem_fixed ρ).mpr (hv coreT), (mem_fixed ρ).mpr (hv coreL)⟩
  · rintro v ⟨hT, hL⟩
    rw [SetLike.mem_coe, mem_fixed] at hT hL
    rw [LinearMap.mem_ker]
    apply cocycle_eq_zero_of_values core_closure
    · change ρ coreT v - v = 0
      rw [hT, sub_self]
    · change ρ coreL v - v = 0
      rw [hL, sub_self]

/-- **Exact `H¹` of `Γ₁(3)`**: `dim H¹ + dim V^E = dim V + dim V^{Γ₁(3)}`. -/
theorem finrank_H1_core_eq :
    finrank ℂ (CrossedH1 ρ) + finrank ℂ (fixed ρ coreE) =
      finrank ℂ V + finrank ℂ (fixed ρ coreT ⊓ fixed ρ coreL : Submodule ℂ V) := by
  have := cocycles_finiteDimensional (ρ := ρ) core_closure core_elliptic_cube
  have equation := finrank_H1_add_finrank_eq (ρ := ρ)
  rw [finrank_cocycles_core, ker_boundary_core] at equation
  have norm := finrank_ker_norm3 ρ
  omega

omit [FiniteDimensional ℂ V] in
theorem normalizedValue_surjective :
    Function.Surjective (normalizedValue (ρ := ρ) (T := coreT) (L := coreL) core_elliptic_cube) := by
  rintro ⟨w, hw, hK⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hK
  have hb : norm3 ρ coreE (-ρ coreE w) = 0 := by
    rw [map_neg, norm3_rho core_elliptic_cube, hK, neg_zero]
  obtain ⟨z, hT, hE⟩ := exists_cocycle ρ 0 (-ρ coreE w) hb
  have hL : z.val coreL = w := by
    have h := cocycle_elliptic coreT coreL z
    change z.val coreE = _ at h
    rw [hE, hT, zero_sub, neg_inj] at h
    have := congrArg (ρ coreE⁻¹) h
    rw [TwoGenerator.rho_inv_apply, TwoGenerator.rho_inv_apply] at this
    exact this.symm
  refine ⟨⟨z, hT, hL ▸ hw⟩, ?_⟩
  apply Subtype.ext
  exact hL

/-- **Exact parabolic `H¹` of `Γ₁(3)`**: with no invariants and no coinvariants,
`dim H¹_par + dim V^T + dim V^L + dim V^E = dim V`. -/
theorem finrank_parabolicH1_core_eq (invariants : fixed ρ coreT ⊓ fixed ρ coreL = ⊥)
    (coinvariants : moved ρ coreT ⊔ moved ρ coreL = ⊤) :
    finrank ℂ (parabolicH1 ρ coreT coreL) + finrank ℂ (fixed ρ coreT) + finrank ℂ (fixed ρ coreL) +
      finrank ℂ (fixed ρ coreE) = finrank ℂ V := by
  apply le_antisymm
    (finrank_parabolicH1_add_le core_closure core_elliptic_cube invariants coinvariants)
  have := cocycles_finiteDimensional (ρ := ρ) core_closure core_elliptic_cube
  let N := normalizedCocycles ρ coreT coreL
  have parabolic_eq : parabolicH1 ρ coreT coreL = N.map (crossedBoundaries ρ).mkQ := by
    apply le_antisymm parabolicH1_le_normalized
    apply Submodule.map_mono
    intro z hz
    refine ⟨?_, hz.2⟩
    rw [hz.1]
    exact Submodule.zero_mem _
  let classes : N →ₗ[ℂ] CrossedH1 ρ := (crossedBoundaries ρ).mkQ.comp N.subtype
  have range_eq : LinearMap.range classes = N.map (crossedBoundaries ρ).mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  let boundaryT : fixed ρ coreT →ₗ[ℂ] N :=
    LinearMap.codRestrict N ((crossedBoundary ρ).comp (fixed ρ coreT).subtype) (by
      intro v
      refine ⟨?_, sub_mem_moved ρ coreL v.val⟩
      change ρ coreT v.val - v.val = 0
      rw [(mem_fixed ρ).mp v.property, sub_self])
  have kernel_le : LinearMap.ker classes ≤ LinearMap.range boundaryT := by
    intro z hz
    rw [LinearMap.mem_ker] at hz
    change (crossedBoundaries ρ).mkQ z.val = 0 at hz
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
    obtain ⟨v, hv⟩ := hz
    have hvT : v ∈ fixed ρ coreT := by
      rw [mem_fixed]
      have h := congrArg (fun c : crossedCocycles ρ => c.val coreT) hv
      change ρ coreT v - v = z.val.val coreT at h
      rw [z.property.1, sub_eq_zero] at h
      exact h
    exact ⟨⟨v, hvT⟩, Subtype.ext hv⟩
  have : IsNoetherian ℂ N := (IsNoetherian.iff_fg (K := ℂ) (V := N)).mpr inferInstance
  have kernel_bound : finrank ℂ (LinearMap.ker classes) ≤ finrank ℂ (fixed ρ coreT) :=
    (Submodule.finrank_mono kernel_le).trans (LinearMap.finrank_range_le boundaryT)
  have rank_nullity := LinearMap.finrank_range_add_finrank_ker (K := ℂ)
    (V := N) (V₂ := CrossedH1 ρ) classes
  rw [range_eq, ← parabolic_eq] at rank_nullity
  have normalized := (LinearEquiv.ofBijective _
    ⟨normalizedValue_injective (ρ := ρ) core_closure core_elliptic_cube,
      normalizedValue_surjective ρ⟩).finrank_eq
  have sup_inf := Submodule.finrank_sup_add_finrank_inf_eq (moved ρ coreL)
    (LinearMap.ker (norm3 ρ coreE))
  rw [moved_sup_ker_norm3 core_elliptic_cube coinvariants, finrank_top] at sup_inf
  have movedL := finrank_moved_add (ρ := ρ) coreL
  have norm := finrank_ker_norm3 ρ
  change finrank ℂ N = _ at normalized
  have e1 : finrank ℂ (fixed ρ coreE) = finrank ℂ (fixed ρ (coreT * coreL⁻¹)) := rfl
  have e2 : finrank ℂ (moved ρ coreL ⊓ LinearMap.ker (norm3 ρ coreE) : Submodule ℂ V) =
      finrank ℂ (moved ρ coreL ⊓ LinearMap.ker (norm3 ρ (coreT * coreL⁻¹)) : Submodule ℂ V) := rfl
  omega

end Exact

section Symmetric

open ParabolicBounds SymFixed

variable {m : ℕ} (e : ℤ)

/-- **`dim H¹(Γ₁(3), Sym^m ⊗ det^e) = 2⌊(m + 2)/3⌋`** for `m > 0`. -/
theorem finrank_core_H1_sym_eq (positive : 0 < m) :
    finrank ℂ (CrossedH1 (coreRep m e)) = 2 * ((m + 2) / 3) := by
  have h := finrank_H1_core_eq (coreRep m e)
  rw [core_invariants e positive, finrank_bot, finrank_fixed_core_E, finrank_sym] at h
  have count := ellipticCount_add m
  omega

/-- **`dim H¹_par(Γ₁(3), Sym^m ⊗ det^e) = 2(⌊(m + 2)/3⌋ - 1)`** for `m > 0`. -/
theorem finrank_core_parabolicH1_sym_eq (positive : 0 < m) :
    finrank ℂ (parabolicH1 (coreRep m e) coreT coreL) + 2 = 2 * ((m + 2) / 3) := by
  have h := finrank_parabolicH1_core_eq (coreRep m e) (core_invariants e positive)
    (core_coinvariants e positive)
  rw [fixed_T, fixed_L, finrank_fixed_upper e one_ne_zero, finrank_fixed_lower e three_ne_zero,
    finrank_fixed_core_E, finrank_sym] at h
  have count := ellipticCount_add m
  omega

end Symmetric

end TernaryPeriodPolynomials.LevelThree.Existence
