module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.OneCocyclePullback

@[expose] public section


/-!
# Mayer–Vietoris for `SL₂(ℤ) = ⟨S⟩ *_{⟨S²⟩} ⟨U⟩` in degree one

For every complex representation `W` of `SL₂(ℤ)`, with `S` of order four, `U = ST` of order six and
`S² = U³ = -1`, the map sending `w ∈ W^{S²}` to the class of the crossed homomorphism `z_w` with
`z_w(S) = 0`, `z_w(U) = Uw - w` is surjective onto `H¹(SL₂(ℤ), W)` with kernel `W^S + W^U`.
Consequently, for finite-dimensional `W`,
`dim H¹ + dim W^S + dim W^U = dim W^{S²} + dim (W^S ⊓ W^U)`, and `W^S ⊓ W^U = W^{SL₂(ℤ)}`.

This is the cohomological half of the level-one Eichler–Shimura dimension count (Mathlib supplies
`ModularForm.dimension_level_one`); it is needed to identify the good-cusp Levi cohomology
`H¹(GL₂(ℤ), H¹(U, V))` with cusp forms.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Spectral.ModularH1

open TernaryPeriodPolynomials.SphericalDetection.Helpers Matrix CategoryTheory
open TernaryPeriodPolynomials.Spectral.ModularH2

abbrev Modular := SpecialLinearGroup (Fin 2) ℤ

variable (W : Rep.{0, 0, 0} ℂ Modular)

/-- Vectors fixed by one element. -/
def fixedSpace (g : Modular) : Submodule ℂ W := LinearMap.ker (W.ρ g - 1)

theorem mem_fixedSpace {g : Modular} {w : W} : w ∈ fixedSpace W g ↔ W.ρ g w = w := by
  simp [fixedSpace, sub_eq_zero]

theorem cocycle_mul (z : groupCohomology.cocycles₁ W) (g h : Modular) :
    z (g * h) = W.ρ g (z h) + z g :=
  (groupCohomology.mem_cocycles₁_iff _).mp z.property g h

theorem cocycle_inv (z : groupCohomology.cocycles₁ W) (g : Modular) :
    z g⁻¹ = -W.ρ g⁻¹ (z g) := by
  rw [← map_neg, ← groupCohomology.cocycles₁_map_inv z g, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply]

/-- A one-cocycle of `SL₂(ℤ)` is determined by its values on `S` and `U = ST`. -/
theorem cocycle_ext {z z' : groupCohomology.cocycles₁ W} (hS : z ModularGroup.S = z' ModularGroup.S)
    (hU : z modularOrderSix = z' modularOrderSix) : z = z' := by
  let agree : Subgroup Modular :=
    { carrier := {g | z g = z' g}
      one_mem' := by
        change z 1 = z' 1
        rw [groupCohomology.cocycles₁_map_one, groupCohomology.cocycles₁_map_one]
      mul_mem' := by
        intro g h hg hh
        change z (g * h) = z' (g * h)
        change z g = z' g at hg
        change z h = z' h at hh
        rw [cocycle_mul, cocycle_mul, hg, hh]
      inv_mem' := by
        intro g hg
        change z g⁻¹ = z' g⁻¹
        change z g = z' g at hg
        rw [cocycle_inv, cocycle_inv, hg] }
  have top : agree = ⊤ := by
    apply top_unique
    rw [← modularGenerators_closure]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with rfl | rfl
    · exact hS
    · exact hU
  apply Subtype.ext
  funext g
  have member : g ∈ agree := top ▸ Subgroup.mem_top g
  exact member

/-- Values of a cocycle on powers. -/
theorem cocycle_pow (z : groupCohomology.cocycles₁ W) (g : Modular) (k : ℕ) :
    z (g ^ k) = ∑ i ∈ Finset.range k, W.ρ (g ^ i) (z g) := by
  induction k with
  | zero => simp [groupCohomology.cocycles₁_map_one]
  | succ k ih =>
    rw [pow_succ, cocycle_mul, ih, Finset.sum_range_succ, add_comm]


theorem rho_rho (g h : Modular) (v : W) : W.ρ g (W.ρ h v) = W.ρ (g * h) v := by
  rw [map_mul, Module.End.mul_apply]

section Construction

/-- The zero two-cocycle; its extension group is the semidirect product `W ⋊ SL₂(ℤ)`. -/
abbrev zeroCycle : groupCohomology.cocycles₂ W := 0

theorem zeroCycle_unit : (zeroCycle W) (1, 1) = 0 := rfl

theorem zeroCycle_apply (pair : Modular × Modular) : (zeroCycle W) pair = 0 := rfl

/-- The semidirect product `W ⋊ SL₂(ℤ)`. -/
abbrev Semidirect := TwoCocycleExtension W (zeroCycle W) (zeroCycle_unit W)

theorem pure_pow (g : Modular) (k : ℕ) :
    (⟨0, g⟩ : Semidirect W) ^ k = ⟨0, g ^ k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, ih]
    apply TwoCocycleExtension.ext
    · change (0 : W) + W.ρ (g ^ k) 0 + (zeroCycle W) (g ^ k, g) = 0
      rw [zeroCycle_apply, map_zero, add_zero, add_zero]
    · exact (pow_succ g k).symm

theorem modularLiftSection_first {G : Type} [Group G] (projection : G →* Modular)
    (first second : G) (first_image : projection first = ModularGroup.S)
    (second_image : projection second = modularOrderSix)
    (fourth : first ^ 4 = 1) (relation : second ^ 3 = first ^ 2) :
    modularLiftSection projection first second first_image second_image fourth relation
      ModularGroup.S = first := by
  have key : (MulEquiv.ofBijective (projection.comp (Subgroup.closure ({first, second} : Set G)).subtype)
      (modularLift_bijective projection first second first_image second_image fourth relation)).symm
        ModularGroup.S = ⟨first, Subgroup.subset_closure (by simp)⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact first_image.symm
  change ((MulEquiv.ofBijective _ _).symm ModularGroup.S : Subgroup.closure ({first, second} : Set G)).val = first
  rw [key]

theorem modularLiftSection_second {G : Type} [Group G] (projection : G →* Modular)
    (first second : G) (first_image : projection first = ModularGroup.S)
    (second_image : projection second = modularOrderSix)
    (fourth : first ^ 4 = 1) (relation : second ^ 3 = first ^ 2) :
    modularLiftSection projection first second first_image second_image fourth relation
      modularOrderSix = second := by
  have key : (MulEquiv.ofBijective (projection.comp (Subgroup.closure ({first, second} : Set G)).subtype)
      (modularLift_bijective projection first second first_image second_image fourth relation)).symm
        modularOrderSix = ⟨second, Subgroup.subset_closure (by simp)⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact second_image.symm
  change ((MulEquiv.ofBijective _ _).symm modularOrderSix : Subgroup.closure ({first, second} : Set G)).val = second
  rw [key]

theorem pureS_projection :
    twoCocycleExtensionProjection W (zeroCycle W) (zeroCycle_unit W) ⟨0, ModularGroup.S⟩ =
      ModularGroup.S := rfl

theorem pureS_fourth : (⟨0, ModularGroup.S⟩ : Semidirect W) ^ 4 = 1 := by
  rw [pure_pow, modularOrderFour]
  rfl

variable {W}

/-- The lift of `U` conjugated by `w`. -/
def liftU (w : W) : Semidirect W :=
  incl W (zeroCycle W) (zeroCycle_unit W) (-w) * ⟨0, modularOrderSix⟩ *
    incl W (zeroCycle W) (zeroCycle_unit W) w

theorem liftU_coefficient (w : W) : (liftU w).coefficient = W.ρ modularOrderSix w - w := by
  unfold liftU
  rw [incl_mul, mul_incl, incl_mul]
  change W.ρ modularOrderSix w + (-w + 0) = _
  abel

theorem liftU_projection (w : W) :
    twoCocycleExtensionProjection W (zeroCycle W) (zeroCycle_unit W) (liftU w) = modularOrderSix := by
  unfold liftU
  rw [map_mul, map_mul, twoCocycleExtensionInclusion_projection,
    twoCocycleExtensionInclusion_projection, one_mul, mul_one]
  rfl

theorem liftU_cube (w : W) (hw : W.ρ (ModularGroup.S ^ 2) w = w) :
    liftU w ^ 3 = (⟨0, ModularGroup.S⟩ : Semidirect W) ^ 2 := by
  have conj : liftU w = (incl W (zeroCycle W) (zeroCycle_unit W) w)⁻¹ * ⟨0, modularOrderSix⟩ *
      ((incl W (zeroCycle W) (zeroCycle_unit W) w)⁻¹)⁻¹ := by
    rw [inv_inv, ← incl_neg]
    rfl
  rw [conj, conj_pow, inv_inv, pure_pow, pure_pow, modularOrderSix_cube, mul_assoc,
    mul_incl]
  change (incl W (zeroCycle W) (zeroCycle_unit W) w)⁻¹ *
    (incl W (zeroCycle W) (zeroCycle_unit W) (W.ρ (ModularGroup.S ^ 2) w) * ⟨0, ModularGroup.S ^ 2⟩) = _
  rw [hw, inv_mul_cancel_left]

/-- The splitting of `W ⋊ SL₂(ℤ)` sending `S ↦ (0, S)` and `U ↦ (Uw - w, U)`. -/
def liftSection (w : W) (hw : W.ρ (ModularGroup.S ^ 2) w = w) : Modular →* Semidirect W :=
  modularLiftSection (twoCocycleExtensionProjection W (zeroCycle W) (zeroCycle_unit W))
    ⟨0, ModularGroup.S⟩ (liftU w) (pureS_projection W) (liftU_projection w)
    (pureS_fourth W) (liftU_cube w hw)

theorem liftSection_element (w : W) (hw : W.ρ (ModularGroup.S ^ 2) w = w) (g : Modular) :
    (liftSection w hw g).element = g :=
  modularLiftSection_projection (twoCocycleExtensionProjection W (zeroCycle W) (zeroCycle_unit W))
    _ _ (pureS_projection W) (liftU_projection w) (pureS_fourth W) (liftU_cube w hw) g

/-- The crossed homomorphism `z_w`: `z_w(S) = 0`, `z_w(U) = Uw - w`, for `w ∈ W^{S²}`. -/
def boundaryCocycle (w : W) (hw : W.ρ (ModularGroup.S ^ 2) w = w) : groupCohomology.cocycles₁ W :=
  ⟨fun g => (liftSection w hw g).coefficient, by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h
    have equation := congrArg TwoCocycleExtension.coefficient ((liftSection w hw).map_mul g h)
    change (liftSection w hw (g * h)).coefficient = (liftSection w hw g).coefficient +
      W.ρ (liftSection w hw g).element (liftSection w hw h).coefficient +
        (zeroCycle W) ((liftSection w hw g).element, (liftSection w hw h).element) at equation
    rw [liftSection_element, liftSection_element] at equation
    change (liftSection w hw (g * h)).coefficient = W.ρ g (liftSection w hw h).coefficient +
      (liftSection w hw g).coefficient
    rw [equation, zeroCycle_apply, add_zero, add_comm]⟩

theorem boundaryCocycle_S (w : W) (hw : W.ρ (ModularGroup.S ^ 2) w = w) :
    boundaryCocycle w hw ModularGroup.S = 0 := by
  change (liftSection w hw ModularGroup.S).coefficient = 0
  unfold liftSection
  rw [modularLiftSection_first]

theorem boundaryCocycle_U (w : W) (hw : W.ρ (ModularGroup.S ^ 2) w = w) :
    boundaryCocycle w hw modularOrderSix = W.ρ modularOrderSix w - w := by
  change (liftSection w hw modularOrderSix).coefficient = _
  unfold liftSection
  rw [modularLiftSection_second, liftU_coefficient]

end Construction


section Classes

variable {W}

theorem boundaryCocycle_add (v w : W) (hv : W.ρ (ModularGroup.S ^ 2) v = v)
    (hw : W.ρ (ModularGroup.S ^ 2) w = w) (hvw : W.ρ (ModularGroup.S ^ 2) (v + w) = v + w) :
    boundaryCocycle (v + w) hvw = boundaryCocycle v hv + boundaryCocycle w hw := by
  apply cocycle_ext W
  · change boundaryCocycle (v + w) hvw ModularGroup.S =
      boundaryCocycle v hv ModularGroup.S + boundaryCocycle w hw ModularGroup.S
    rw [boundaryCocycle_S, boundaryCocycle_S, boundaryCocycle_S, add_zero]
  · change boundaryCocycle (v + w) hvw modularOrderSix =
      boundaryCocycle v hv modularOrderSix + boundaryCocycle w hw modularOrderSix
    rw [boundaryCocycle_U, boundaryCocycle_U, boundaryCocycle_U, map_add]
    abel

theorem boundaryCocycle_smul (c : ℂ) (v : W) (hv : W.ρ (ModularGroup.S ^ 2) v = v)
    (hcv : W.ρ (ModularGroup.S ^ 2) (c • v) = c • v) :
    boundaryCocycle (c • v) hcv = c • boundaryCocycle v hv := by
  apply cocycle_ext W
  · change boundaryCocycle (c • v) hcv ModularGroup.S = c • boundaryCocycle v hv ModularGroup.S
    rw [boundaryCocycle_S, boundaryCocycle_S, smul_zero]
  · change boundaryCocycle (c • v) hcv modularOrderSix = c • boundaryCocycle v hv modularOrderSix
    rw [boundaryCocycle_U, boundaryCocycle_U, map_smul, smul_sub]

variable (W)

/-- The `S² = -1`-fixed vectors. -/
abbrev centralFixed : Submodule ℂ W := fixedSpace W (ModularGroup.S ^ 2)

/-- `w ↦ z_w` as a linear map `W^{S²} → Z¹(SL₂(ℤ), W)`. -/
def boundaryCocycleMap : centralFixed W →ₗ[ℂ] groupCohomology.cocycles₁ W where
  toFun w := boundaryCocycle w.val ((mem_fixedSpace W).mp w.property)
  map_add' _ _ := boundaryCocycle_add _ _ _ _ _
  map_smul' _ _ := boundaryCocycle_smul _ _ _ _

/-- The connecting map `W^{S²} → H¹(SL₂(ℤ), W)` of the amalgam Mayer–Vietoris sequence. -/
def connecting : centralFixed W →ₗ[ℂ] groupCohomology.H1 W :=
  (groupCohomology.H1π W).hom ∘ₗ boundaryCocycleMap W

theorem connecting_apply (w : centralFixed W) :
    connecting W w = (groupCohomology.H1π W).hom
      (boundaryCocycle w.val ((mem_fixedSpace W).mp w.property)) := rfl

theorem rho_cube_eq (v : W) : W.ρ (ModularGroup.S ^ 2) v = W.ρ modularOrderSix
    (W.ρ modularOrderSix (W.ρ modularOrderSix v)) := by
  rw [← modularOrderSix_cube, rho_rho, rho_rho, pow_succ, pow_two]

/-- Every class is represented by some `z_w`. -/
theorem connecting_surjective : Function.Surjective (connecting W) := by
  intro x
  obtain ⟨z, rfl⟩ := oneCocycle_H1_surjective W x
  set a := z ModularGroup.S with ha
  have hN : a + W.ρ ModularGroup.S a + W.ρ (ModularGroup.S ^ 2) a + W.ρ (ModularGroup.S ^ 3) a = 0 := by
    have h := cocycle_pow W z ModularGroup.S 4
    rw [modularOrderFour, groupCohomology.cocycles₁_map_one] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, map_one,
      Module.End.one_apply, pow_one] at h
    exact h.symm
  have h2 : W.ρ ModularGroup.S (W.ρ ModularGroup.S a) = W.ρ (ModularGroup.S ^ 2) a := by
    rw [rho_rho, pow_two]
  have h3 : W.ρ ModularGroup.S (W.ρ (ModularGroup.S ^ 2) a) = W.ρ (ModularGroup.S ^ 3) a := by
    rw [rho_rho, ← pow_succ']
  have h4 : W.ρ ModularGroup.S (W.ρ (ModularGroup.S ^ 3) a) = a := by
    rw [rho_rho, ← pow_succ', modularOrderFour, map_one, Module.End.one_apply]
  let w0 : W := (4 : ℂ)⁻¹ • (W.ρ ModularGroup.S a + (2 : ℂ) • W.ρ (ModularGroup.S ^ 2) a +
    (3 : ℂ) • W.ρ (ModularGroup.S ^ 3) a)
  have hw0 : W.ρ ModularGroup.S w0 - w0 = a := by
    simp only [w0, map_smul, map_add, h2, h3, h4]
    linear_combination (norm := module) (-(4 : ℂ)⁻¹) • hN
  let z' : groupCohomology.cocycles₁ W := z - oneBoundaryCycle W w0
  have hz'S : z' ModularGroup.S = 0 := by
    change z ModularGroup.S - (W.ρ ModularGroup.S w0 - w0) = 0
    rw [hw0, ← ha, sub_self]
  set b := z' modularOrderSix with hb
  have hz'S2 : z' (ModularGroup.S ^ 2) = 0 := by
    rw [pow_two, cocycle_mul, hz'S, map_zero, add_zero]
  have hcube : b + W.ρ modularOrderSix b + W.ρ (modularOrderSix ^ 2) b = 0 := by
    have h := cocycle_pow W z' modularOrderSix 3
    rw [modularOrderSix_cube, hz'S2] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, map_one,
      Module.End.one_apply, pow_one] at h
    exact h.symm
  have u2 : W.ρ modularOrderSix (W.ρ modularOrderSix b) = W.ρ (modularOrderSix ^ 2) b := by
    rw [rho_rho, pow_two]
  have u3 : W.ρ modularOrderSix (W.ρ (modularOrderSix ^ 2) b) = b := by
    have h := congrArg (W.ρ modularOrderSix) hcube
    rw [map_add, map_add, map_zero, u2] at h
    linear_combination (norm := module) h - hcube
  let w : W := (3 : ℂ)⁻¹ • (W.ρ modularOrderSix b + (2 : ℂ) • W.ρ (modularOrderSix ^ 2) b)
  have hwU : W.ρ modularOrderSix w - w = b := by
    simp only [w, map_smul, map_add, u2, u3]
    linear_combination (norm := module) (-(3 : ℂ)⁻¹) • hcube
  have hwS : W.ρ (ModularGroup.S ^ 2) w = w := by
    have comm : ∀ v : W, W.ρ (ModularGroup.S ^ 2) (W.ρ modularOrderSix v) =
        W.ρ modularOrderSix (W.ρ (ModularGroup.S ^ 2) v) := by
      intro v
      rw [rho_rho, rho_rho, ← modularOrderSix_cube, ← pow_succ, ← pow_succ']
    have fixed_b : W.ρ (ModularGroup.S ^ 2) b = b := by
      rw [rho_cube_eq, u2, u3]
    have fixed_ub : W.ρ (ModularGroup.S ^ 2) (W.ρ modularOrderSix b) = W.ρ modularOrderSix b := by
      rw [comm, fixed_b]
    have fixed_uub : W.ρ (ModularGroup.S ^ 2) (W.ρ (modularOrderSix ^ 2) b) =
        W.ρ (modularOrderSix ^ 2) b := by
      rw [← u2, comm, fixed_ub]
    simp only [w, map_smul, map_add, fixed_ub, fixed_uub]
  refine ⟨⟨w, (mem_fixedSpace W).mpr hwS⟩, ?_⟩
  have heq : boundaryCocycle w hwS = z' :=
    cocycle_ext W (by rw [boundaryCocycle_S, hz'S]) (by rw [boundaryCocycle_U, hwU])
  rw [connecting_apply]
  change (groupCohomology.H1π W).hom (boundaryCocycle w hwS) = _
  rw [heq, map_sub, oneBoundaryCycle_H1_zero, sub_zero]

/-- The kernel of the connecting map is `W^S + W^U`. -/
theorem connecting_eq_zero_iff (w : centralFixed W) :
    connecting W w = 0 ↔ w.val ∈ fixedSpace W ModularGroup.S ⊔ fixedSpace W modularOrderSix := by
  rw [connecting_apply]
  constructor
  · intro zero
    rw [groupCohomology.H1π_eq_zero_iff] at zero
    obtain ⟨v, hv⟩ := zero
    have value : ∀ g, W.ρ g v - v = boundaryCocycle w.val ((mem_fixedSpace W).mp w.property) g :=
      fun g => congrFun hv g
    have hS := value ModularGroup.S
    rw [boundaryCocycle_S, sub_eq_zero] at hS
    have hU := value modularOrderSix
    rw [boundaryCocycle_U] at hU
    have fixed : W.ρ modularOrderSix (w.val - v) = w.val - v := by
      rw [map_sub]
      linear_combination (norm := module) -hU
    have decomposition : w.val = v + (w.val - v) := by abel
    rw [decomposition]
    exact Submodule.add_mem_sup ((mem_fixedSpace W).mpr hS) ((mem_fixedSpace W).mpr fixed)
  · intro member
    obtain ⟨y, hy, t, ht, hyt⟩ := Submodule.mem_sup.mp member
    rw [mem_fixedSpace] at hy ht
    have heq : boundaryCocycle w.val ((mem_fixedSpace W).mp w.property) = oneBoundaryCycle W y := by
      apply cocycle_ext W
      · rw [boundaryCocycle_S]
        change 0 = W.ρ ModularGroup.S y - y
        rw [hy, sub_self]
      · rw [boundaryCocycle_U, ← hyt]
        change W.ρ modularOrderSix (y + t) - (y + t) = W.ρ modularOrderSix y - y
        rw [map_add, ht]
        abel
    rw [heq, oneBoundaryCycle_H1_zero]

theorem fixedS_le_central : fixedSpace W ModularGroup.S ≤ centralFixed W := by
  intro v hv
  rw [mem_fixedSpace] at hv ⊢
  rw [pow_two, map_mul, Module.End.mul_apply, hv, hv]

theorem fixedU_le_central : fixedSpace W modularOrderSix ≤ centralFixed W := by
  intro v hv
  rw [mem_fixedSpace] at hv ⊢
  rw [rho_cube_eq, hv, hv, hv]

/-- Vectors fixed by `S` and `U` are fixed by all of `SL₂(ℤ)`. -/
theorem mem_inf_fixed_iff (v : W) :
    v ∈ fixedSpace W ModularGroup.S ⊓ fixedSpace W modularOrderSix ↔ ∀ g, W.ρ g v = v := by
  constructor
  · rintro ⟨hS, hU⟩ g
    rw [SetLike.mem_coe, mem_fixedSpace] at hS hU
    let fixer : Subgroup Modular :=
      { carrier := {g | W.ρ g v = v}
        one_mem' := by simp
        mul_mem' := by
          intro g h hg hh
          change W.ρ (g * h) v = v
          change W.ρ g v = v at hg
          change W.ρ h v = v at hh
          rw [map_mul, Module.End.mul_apply, hh, hg]
        inv_mem' := by
          intro g hg
          change W.ρ g⁻¹ v = v
          change W.ρ g v = v at hg
          conv_lhs => rw [← hg]
          rw [rho_rho, inv_mul_cancel, map_one, Module.End.one_apply] }
    have top : fixer = ⊤ := by
      apply top_unique
      rw [← modularGenerators_closure]
      apply (Subgroup.closure_le _).mpr
      intro g hg
      rcases hg with rfl | rfl
      · exact hS
      · exact hU
    have member : g ∈ fixer := top ▸ Subgroup.mem_top g
    exact member
  · intro h
    exact ⟨(mem_fixedSpace W).mpr (h _), (mem_fixedSpace W).mpr (h _)⟩

/-- **Mayer–Vietoris dimension count** for `SL₂(ℤ)`:
`dim H¹ + dim W^S + dim W^U = dim W^{S²} + dim W^{SL₂(ℤ)}` (with `W^{SL₂(ℤ)} = W^S ⊓ W^U`). -/
theorem finrank_H1_add [FiniteDimensional ℂ W] :
    Module.finrank ℂ (groupCohomology.H1 W) + Module.finrank ℂ (fixedSpace W ModularGroup.S) +
      Module.finrank ℂ (fixedSpace W modularOrderSix) =
    Module.finrank ℂ (centralFixed W) +
      Module.finrank ℂ ↥(fixedSpace W ModularGroup.S ⊓ fixedSpace W modularOrderSix) := by
  have rank_nullity := LinearMap.finrank_range_add_finrank_ker (connecting W)
  rw [LinearMap.range_eq_top.mpr (connecting_surjective W), finrank_top] at rank_nullity
  have hle : fixedSpace W ModularGroup.S ⊔ fixedSpace W modularOrderSix ≤ centralFixed W :=
    sup_le (fixedS_le_central W) (fixedU_le_central W)
  have hker : LinearMap.ker (connecting W) =
      (fixedSpace W ModularGroup.S ⊔ fixedSpace W modularOrderSix).comap (centralFixed W).subtype := by
    ext w
    rw [LinearMap.mem_ker, connecting_eq_zero_iff, Submodule.mem_comap, Submodule.subtype_apply]
  have kernel_rank : Module.finrank ℂ (LinearMap.ker (connecting W)) =
      Module.finrank ℂ ↥(fixedSpace W ModularGroup.S ⊔ fixedSpace W modularOrderSix) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have sup_inf := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpace W ModularGroup.S)
    (fixedSpace W modularOrderSix)
  omega

end Classes

end TernaryPeriodPolynomials.Spectral.ModularH1
