module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonApartment
public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalDescent
public import TernaryPeriodPolynomials.GroupCohomology.Homology.HomAveraging

@[expose] public section


/-!
# The level-group duality for an arbitrary coefficient module, conditional on equivariance

The generic form of `KLevel`: `Kp` is any group containing a normal finite index subgroup `N`
identified with the neat group `Γ(6)` (`e : N ≃* principalSix`), `σ` is a representation of `Kp` on
the Steinberg module (the ordinary incidence cycles) extending the library's action of `Γ(6)`
(`hσ`), and `M` is an arbitrary `ℚ`-representation of `Kp`.  Everything is as in `KLevel`; the
specific case `Kp = K`, `M = E_{n,t}` is `KLevel.kEquivOfEquivariance`.  The theorem
`kEquivGeneric` is **CONDITIONAL** on `NeatDualityEquivariantGen`, the `Kp`-equivariance of the
library's neat-level duality, which is not proved.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly IntegralGL3Congruence CategoryTheory
  TernaryPeriodPolynomials.Argument.GroupHomology

section Generic

variable {Kp : Type} [Group Kp] (N : Subgroup Kp) (e : N ≃* ↥principalSix)
  (σ : Representation ℚ Kp OrdinaryIncidenceChains.Cycles)
  (M : Rep.{0} ℚ Kp)

/-- `M` transported to `Γ(6)` along `e`. -/
def transportRep : Rep.{0} ℚ principalSix :=
  Rep.of (M.ρ.comp (N.subtype.comp e.symm.toMonoidHom))

/-- The neat-level duality for `M`, transported to `N`. -/
def thetaGen :
    groupHomology (Rep.res N.subtype M) 3 ≅
      OrdinaryTopBoundaryComparison.ordinaryFunctionals (transportRep N e M) :=
  groupHomology.mapIso e (LinearEquiv.refl ℚ M) (fun n => LinearMap.ext fun a => by
    change M.ρ n.1 a = M.ρ (e.symm (e n)).1 a
    rw [MulEquiv.symm_apply_apply]) 3 ≪≫
    OrdinaryTopBoundaryComparison.groupOrdinaryIso (transportRep N e M)

variable [N.Normal] [N.FiniteIndex]
  (hσ : ∀ n : N, σ n = SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep.ρ (e n))

open scoped Classical

/-- The underlying linear map of an equivariant functional. -/
def toLinG (φ : SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep ⟶ transportRep N e M) :
    OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M := φ.hom.toLinearMap

omit [N.Normal] [N.FiniteIndex] in
theorem toLinG_injective :
    Function.Injective (toLinG N e M : (SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep ⟶
      transportRep N e M) → _) := by
  intro φ ψ h
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact h

omit [N.Normal] [N.FiniteIndex] in
include hσ in
theorem toLinG_isEquivOn
    (φ : SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep ⟶ transportRep N e M) :
    GroupHomology.IsEquivOn σ M.ρ N (toLinG N e M φ) := by
  intro g hg z
  have h := Rep.hom_comm_apply φ (e ⟨g, hg⟩) z
  rw [hσ ⟨g, hg⟩]
  change φ.hom (SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep.ρ (e ⟨g, hg⟩) z) =
    M.ρ g (φ.hom z)
  rw [h]
  change M.ρ (e.symm (e ⟨g, hg⟩)).1 (φ.hom z) = _
  rw [MulEquiv.symm_apply_apply]

omit [N.Normal] [N.FiniteIndex] in
include hσ in
theorem exists_toLinG_eq (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M)
    (hΦ : GroupHomology.IsEquivOn σ M.ρ N Φ) :
    ∃ φ : SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep ⟶ transportRep N e M,
      toLinG N e M φ = Φ := by
  refine ⟨Rep.ofHom ⟨Φ, fun γ => LinearMap.ext fun z => ?_⟩, rfl⟩
  have h := hΦ (e.symm γ).1 (e.symm γ).2 z
  rw [hσ (e.symm γ), MulEquiv.apply_symm_apply] at h
  exact h

/-- `toLinG` as a linear map. -/
def toLinGL :
    (SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep ⟶ transportRep N e M) →ₗ[ℚ]
      (OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M) where
  toFun := toLinG N e M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The neat-level duality followed by forgetting equivariance. -/
def psiGen : groupHomology (Rep.res N.subtype M) 3 →ₗ[ℚ]
    (OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M) :=
  toLinGL N e M ∘ₗ (thetaGen N e M).hom.hom

omit [N.Normal] [N.FiniteIndex] in
theorem psiGen_injective : Function.Injective (psiGen N e M) := by
  intro x y h
  have h1 := toLinG_injective N e M h
  have h2 : (thetaGen N e M).hom.hom x = (thetaGen N e M).hom.hom y := h1
  have := congrArg (fun z => (thetaGen N e M).inv.hom z) h2
  simpa using this

omit [N.Normal] [N.FiniteIndex] in
include hσ in
theorem mem_range_psiGen_iff (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M) :
    Φ ∈ LinearMap.range (psiGen N e M) ↔ GroupHomology.IsEquivOn σ M.ρ N Φ := by
  constructor
  · rintro ⟨x, rfl⟩
    exact toLinG_isEquivOn N e σ M hσ _
  · intro hΦ
    obtain ⟨φ, hφ⟩ := exists_toLinG_eq N e σ M hσ Φ hΦ
    refine ⟨(thetaGen N e M).inv.hom φ, ?_⟩
    change toLinG N e M ((thetaGen N e M).hom.hom ((thetaGen N e M).inv.hom φ)) = Φ
    have : (thetaGen N e M).hom.hom ((thetaGen N e M).inv.hom φ) = φ := by simp
    rw [this, hφ]

/-- The `Kp`-equivariant linear maps `St → M`. -/
def homKGen : Submodule ℚ (OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M) where
  carrier := {Φ | ∀ (k : Kp) (z : OrdinaryIncidenceChains.Cycles), Φ (σ k z) = M.ρ k (Φ z)}
  zero_mem' := by intro k z; simp
  add_mem' := by
    intro Φ Ψ hΦ hΨ k z
    simp only [LinearMap.add_apply, hΦ k z, hΨ k z, map_add]
  smul_mem' := by
    intro c Φ hΦ k z
    simp only [LinearMap.smul_apply, hΦ k z, map_smul]

theorem mem_homKGen_iff (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M) :
    Φ ∈ homKGen σ M ↔ GroupHomology.IsEquivOn σ M.ρ ⊤ Φ :=
  ⟨fun h k _ z => h k z, fun h k z => h k trivial z⟩

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

omit [N.Normal] in
theorem card_ne_zero_gen : (Fintype.card (Kp ⧸ N) : ℚ) ≠ 0 := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero

/-- **The `Kp`-equivariance of the neat-level duality** for the module `M` (the hypothesis of the
CONDITIONAL theorem `kEquivGeneric`; not proved). -/
def NeatDualityEquivariantGen : Prop :=
  ∀ (g : Kp) (x : groupHomology (Rep.res N.subtype M) 3),
    psiGen N e M (cAct N M 3 g x) = GroupHomology.actL σ M.ρ g (psiGen N e M x)

variable {N e σ M}

theorem psiGen_avgN (h : NeatDualityEquivariantGen N e σ M)
    (x : groupHomology (Rep.res N.subtype M) 3) :
    psiGen N e M (avgN N M 3 x) = GroupHomology.avg σ M.ρ N (psiGen N e M x) := by
  have h' : ∀ (g : Kp) (x : groupHomology (Rep.res N.subtype M) 3),
      psiGen N e M (cAct N M 3 g x) = GroupHomology.actL σ M.ρ g (psiGen N e M x) := h
  rw [GroupHomology.avg_eq_sum]
  unfold avgN
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, h']

theorem psiGen_avgN_mem (hσ : ∀ n : N, σ n = SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep.ρ (e n))
    (h : NeatDualityEquivariantGen N e σ M) (x : groupHomology (Rep.res N.subtype M) 3) :
    psiGen N e M (avgN N M 3 x) ∈ homKGen σ M := by
  rw [psiGen_avgN h, mem_homKGen_iff]
  exact GroupHomology.avg_isEquiv ((mem_range_psiGen_iff N e σ M hσ _).mp ⟨x, rfl⟩)

theorem corN_avgN_gen (x : groupHomology (Rep.res N.subtype M) 3) :
    corN N M 3 (avgN N M 3 x) = corN N M 3 x := by
  unfold avgN
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, corN_cAct,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (card_ne_zero_gen N), one_smul]

/-- **CONDITIONAL.**  If the neat-level duality is `Kp`-equivariant, then
`H₃(Kp, M) ≃ Hom_{Kp}(St, M)`. -/
def kEquivGeneric (hσ : ∀ n : N, σ n = SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep.ρ (e n))
    (h : NeatDualityEquivariantGen N e σ M) :
    groupHomology M 3 ≃ₗ[ℚ] homKGen σ M :=
  let E := LinearMap.range (avgN N M 3)
  have hfix : ∀ z ∈ E, avgN N M 3 z = z := by
    rintro _ ⟨w, rfl⟩
    exact avgN_idem (card_ne_zero_gen N) w
  let corE : E →ₗ[ℚ] groupHomology M 3 := (corN N M 3).domRestrict E
  let psiE : E →ₗ[ℚ] homKGen σ M :=
    LinearMap.codRestrict (homKGen σ M) ((psiGen N e M).domRestrict E) (by
      rintro ⟨_, w, rfl⟩
      exact psiGen_avgN_mem hσ h w)
  have hcorInj : Function.Injective corE := by
    intro z z' hzz
    have h1 : corN N M 3 (z.1 - z'.1) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hzz
    have h2 := (corN_eq_zero_iff (card_ne_zero_gen N) _).mp h1
    have h3 : avgN N M 3 (z.1 - z'.1) = z.1 - z'.1 := by
      rw [map_sub, hfix _ z.2, hfix _ z'.2]
    exact Subtype.ext (sub_eq_zero.mp (h3 ▸ h2))
  have hcorSurj : Function.Surjective corE := by
    intro w
    obtain ⟨z, rfl⟩ := corN_surjective (A := M) (n := 3) (card_ne_zero_gen N) w
    exact ⟨⟨avgN N M 3 z, z, rfl⟩, corN_avgN_gen z⟩
  have hpsiInj : Function.Injective psiE := fun z z' hzz =>
    Subtype.ext (psiGen_injective N e M (congrArg Subtype.val hzz))
  have hpsiSurj : Function.Surjective psiE := by
    rintro ⟨Ψ, hΨ⟩
    have hΨ' := (mem_homKGen_iff σ M Ψ).mp hΨ
    obtain ⟨y, hy⟩ := (mem_range_psiGen_iff N e σ M hσ Ψ).mpr (fun g hg z => hΨ' g trivial z)
    refine ⟨⟨avgN N M 3 y, y, rfl⟩, Subtype.ext ?_⟩
    change psiGen N e M (avgN N M 3 y) = Ψ
    rw [psiGen_avgN h, hy]
    exact GroupHomology.avg_of_isEquiv_natCard hΨ' (by
      rw [Nat.card_eq_fintype_card]; exact card_ne_zero_gen N)
  (LinearEquiv.ofBijective corE ⟨hcorInj, hcorSurj⟩).symm.trans
    (LinearEquiv.ofBijective psiE ⟨hpsiInj, hpsiSurj⟩)

end Generic

end TernaryPeriodPolynomials.Argument.FiberModel
