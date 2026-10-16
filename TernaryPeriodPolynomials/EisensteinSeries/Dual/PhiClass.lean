module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Bridge
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.TransferBack

@[expose] public section


open CategoryTheory

/-!
# Transport of homogeneous classes along an involutive endomorphism, and its compatibility with the transfer and the bridge

Formalized by Claude Sonnet 5.5.

For an involutive endomorphism `α` of the ambient group `G` and representations `ρ' = ρ ∘ α`, the pullback `c ↦ c ∘ α` of homogeneous cochains carries
`N`-equivariant classes (`ρ`) to `N'`-equivariant classes (`ρ'`), `N' = α⁻¹ N`.  It is natural for the Mathlib bridge (`bridge_phiH2`) and for the transfer
`trH2` of a normal finite-index subgroup (`trH2_phiH2`).  Used in `DualClassK` for `α = φ`, the level-preserving involution of the dual coefficient system.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Argument.LevelTransfer
  TernaryPeriodPolynomials.Argument.SeedC3S4c

section Phi

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (α : G →* G) (ρ ρ' : Representation ℂ G V) (hρ : ∀ g, ρ' g = ρ (α g))

/-- The pullback of raw functions along `α`. -/
def phiFun {k : ℕ} : FunSpace G V k →ₗ[ℂ] FunSpace G V k where
  toFun f x := f (fun i => α (x i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem phiFun_apply {k : ℕ} (f : FunSpace G V k) (x : Fin (k + 1) → G) :
    phiFun α f x = f (fun i => α (x i)) := rfl

theorem phiFun_rd1 (f : FunSpace G V 1) : phiFun α (rd1 f) = rd1 (phiFun α f) := by
  funext x
  have h : ∀ a b : Fin 3, (fun i : Fin 2 => α ((![x a, x b] : Fin 2 → G) i)) = ![α (x a), α (x b)] := by
    intro a b; funext i; fin_cases i <;> rfl
  simp only [phiFun_apply, rd1, LinearMap.coe_mk, AddHom.coe_mk, h]

theorem phiFun_rd2 (f : FunSpace G V 2) : phiFun α (rd2 f) = rd2 (phiFun α f) := by
  funext x
  have h : ∀ a b c : Fin 4, (fun i : Fin 3 => α ((![x a, x b, x c] : Fin 3 → G) i)) = ![α (x a), α (x b), α (x c)] := by
    intro a b c; funext i; fin_cases i <;> rfl
  simp only [phiFun_apply, rd2, LinearMap.coe_mk, AddHom.coe_mk, h]

variable (N N' : Subgroup G) (hN : ∀ x, x ∈ N' ↔ α x ∈ N)

include hρ hN in
theorem isEq_phiFun {k : ℕ} {f : FunSpace G V k} (hf : IsEq ρ N f) : IsEq ρ' N' (phiFun α f) := by
  intro γ hγ x
  have h1 : (fun i => α (γ * x i)) = fun i => α γ * α (x i) := by
    funext i; exact map_mul α _ _
  rw [phiFun_apply, phiFun_apply, h1, hf (α γ) ((hN γ).1 hγ), hρ]

/-- The pullback of equivariant cochains. -/
def phiCochain (k : ℕ) : cochains N ρ k →ₗ[ℂ] cochains N' ρ' k where
  toFun f := ⟨phiFun α f.val, (mem_cochains_iff ρ' N' k _).2 (isEq_phiFun α ρ ρ' hρ N N' hN ((mem_cochains_iff ρ N k _).1 f.property))⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The pullback of cocycles. -/
def phiCocycleN : cocycles N ρ →ₗ[ℂ] cocycles N' ρ' where
  toFun c := ⟨phiCochain α ρ ρ' hρ N N' hN 2 c.val, by
    have h : differentialTwo N ρ c.val = 0 := c.property
    change differentialTwo N' ρ' (phiCochain α ρ ρ' hρ N N' hN 2 c.val) = 0
    rw [differentialTwo_eq] at h ⊢
    change rd2 (phiFun α c.val.val) = 0
    rw [← phiFun_rd2]
    rw [show rd2 c.val.val = 0 from h]
    rfl⟩
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

theorem phiCocycleN_val (c : cocycles N ρ) (x : Fin 3 → G) :
    (phiCocycleN α ρ ρ' hρ N N' hN c).val.val x = c.val.val (fun i => α (x i)) := rfl

/-- The pullback of classes, `H²(N, ρ) → H²(α⁻¹N, ρ ∘ α)`. -/
def phiH2 : H2 N ρ →ₗ[ℂ] H2 N' ρ' :=
  Submodule.mapQ _ _ (phiCocycleN α ρ ρ' hρ N N' hN) (by
    rintro _ ⟨c, rfl⟩
    refine ⟨phiCochain α ρ ρ' hρ N N' hN 1 c, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (phiFun_rd1 α c.val).symm)

theorem phiH2_mk (z : cocycles N ρ) :
    phiH2 α ρ ρ' hρ N N' hN (Submodule.Quotient.mk z) = Submodule.Quotient.mk (phiCocycleN α ρ ρ' hρ N N' hN z) := rfl

end Phi


section Avg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (α : G →* G) (hα : ∀ g, α (α g) = g) (ρ ρ' : Representation ℂ G V) (hρ : ∀ g, ρ' g = ρ (α g))

include hρ in
theorem actFun_phiFun (s : G) {k : ℕ} (f : FunSpace G V k) :
    actFun ρ' s (phiFun α f) = phiFun α (actFun ρ (α s) f) := by
  funext x
  simp only [actFun_apply, phiFun_apply, hρ, map_mul, map_inv]

theorem actFun_congr {N : Subgroup G} {k : ℕ} {f : FunSpace G V k} (hf : IsEq ρ N f) {s s' : G}
    (h : s⁻¹ * s' ∈ N) : actFun ρ s' f = actFun ρ s f := by
  have e : s' = s * (s⁻¹ * s') := by group
  rw [e, actFun_mul, IsEq.act_mem ρ hf h]

variable (N N' S : Subgroup G) (hN : ∀ x, x ∈ N' ↔ α x ∈ N) (hS : ∀ x, x ∈ S ↔ α x ∈ S)

/-- `α` restricted to `S`. -/
def alphaS : S →* S where
  toFun s := ⟨α (s : G), (hS s).1 s.2⟩
  map_one' := Subtype.ext (by
    show α ((1 : S) : G) = ((1 : S) : G)
    simp)
  map_mul' a b := Subtype.ext (by
    show α ((a * b : S) : G) = α (a : G) * α (b : G)
    simp)

include hα in
theorem alphaS_alphaS (s : S) : alphaS α S hS (alphaS α S hS s) = s := Subtype.ext (hα s)

/-- The induced bijection `S/N' ≃ S/N`. -/
def quotEquiv : (S ⧸ N'.subgroupOf S) ≃ (S ⧸ N.subgroupOf S) where
  toFun := Quotient.map' (alphaS α S hS) (fun a b hab => by
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab ⊢
    have := (hN _).1 hab
    simpa [alphaS, map_mul, map_inv] using this)
  invFun := Quotient.map' (alphaS α S hS) (fun a b hab => by
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab ⊢
    refine (hN _).2 ?_
    simpa [alphaS, map_mul, map_inv, hα] using hab)
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => exact congrArg Quotient.mk'' (alphaS_alphaS α hα S hS a)
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => exact congrArg Quotient.mk'' (alphaS_alphaS α hα S hS a)

theorem quotEquiv_mk (a : S) :
    quotEquiv α hα N N' S hN hS (QuotientGroup.mk a) = QuotientGroup.mk (alphaS α S hS a) := rfl

include hα hρ hN hS in
/-- **The averaging operator commutes with the pullback along `α`.** -/
theorem avg_phiFun [Fintype (S ⧸ N.subgroupOf S)] [Fintype (S ⧸ N'.subgroupOf S)] {k : ℕ}
    {f : FunSpace G V k} (hf : IsEq ρ N f) :
    avg ρ' N' S (phiFun α f) = phiFun α (avg ρ N S f) := by
  rw [avg_apply, avg_apply]
  have hcard : Fintype.card (S ⧸ N'.subgroupOf S) = Fintype.card (S ⧸ N.subgroupOf S) :=
    Fintype.card_congr (quotEquiv α hα N N' S hN hS)
  rw [hcard, map_smul, map_sum]
  congr 1
  simp only [actFun_phiFun α ρ ρ' hρ]
  refine Fintype.sum_equiv (quotEquiv α hα N N' S hN hS) _ _ (fun q => ?_)
  congr 1
  apply actFun_congr ρ hf
  have h1 : (QuotientGroup.mk (s := N.subgroupOf S) (Quotient.out (quotEquiv α hα N N' S hN hS q))) =
      QuotientGroup.mk (s := N.subgroupOf S) (alphaS α S hS (Quotient.out q)) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h2 := QuotientGroup.eq.mp h1
  rw [Subgroup.mem_subgroupOf] at h2
  simpa [alphaS] using h2

end Avg


section Tr

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (α : G →* G) (hα : ∀ g, α (α g) = g) (ρ ρ' : Representation ℂ G V) (hρ : ∀ g, ρ' g = ρ (α g))
  (N N' S : Subgroup G) (hN : ∀ x, x ∈ N' ↔ α x ∈ N) (hS : ∀ x, x ∈ S ↔ α x ∈ S)
  [Fintype (S ⧸ N.subgroupOf S)] [Fintype (S ⧸ N'.subgroupOf S)]
  (hNS : N ≤ S) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s⁻¹ * n * s ∈ N)
  (hN'S : N' ≤ S) (hnorm' : ∀ s ∈ S, ∀ n ∈ N', s⁻¹ * n * s ∈ N')

include hα hρ hN hS in
/-- **The transfer commutes with the pullback along `α`** (the averaging is reindexed by the induced bijection `S/N' ≃ S/N`). -/
theorem trH2_phiH2 (y : H2 N ρ) :
    trH2 ρ' hN'S hnorm' (phiH2 α ρ ρ' hρ N N' hN y) = phiH2 α ρ ρ' hρ S S hS (trH2 ρ hNS hnorm y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change Submodule.Quotient.mk (avgCocycle ρ' hN'S hnorm' (phiCocycleN α ρ ρ' hρ N N' hN z)) =
    Submodule.Quotient.mk (phiCocycleN α ρ ρ' hρ S S hS (avgCocycle ρ hNS hnorm z))
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact avg_phiFun α hα ρ ρ' hρ N N' S hN hS ((mem_cochains_iff ρ N 2 _).1 z.val.property)

end Tr

section BridgeNat

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (α : G →* G) (ρ ρ' : Representation ℂ G V) (hρ : ∀ g, ρ' g = ρ (α g))
  (N N' : Subgroup G) (hN : ∀ x, x ∈ N' ↔ α x ∈ N)

/-- `α` as a homomorphism `N' → N`. -/
def alphaSub : N' →* N where
  toFun x := ⟨α (x : G), (hN x).1 x.2⟩
  map_one' := Subtype.ext (by
    show α ((1 : N') : G) = ((1 : N) : G)
    simp)
  map_mul' a b := Subtype.ext (by
    show α ((a * b : N') : G) = α (a : G) * α (b : G)
    simp)

/-- The identity intertwiner over `α`. -/
def phiCoeff : Rep.res (alphaSub α N N' hN) (Rep.of (ρ.comp N.subtype)) ⟶ Rep.of (ρ'.comp N'.subtype) :=
  Rep.ofHom ⟨LinearMap.id, fun g => by
    ext v
    exact (congrArg (fun L => L v) (hρ g.1)).symm⟩

/-- **Naturality of the bridge** for the pullback along `α`. -/
theorem bridge_phiH2 (y : H2 N ρ) :
    bridge ρ' N' (phiH2 α ρ ρ' hρ N N' hN y) =
      (groupCohomology.map (alphaSub α N N' hN) (phiCoeff α ρ ρ' hρ N N' hN) 2).hom (bridge ρ N y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [phiH2_mk, bridge_mk, bridge_mk]
  have h2 := congrArg (fun t => t.hom (bridgeCocycle ρ N z))
    (groupCohomology.H2π_comp_map (alphaSub α N N' hN) (phiCoeff α ρ ρ' hρ N N' hN))
  change (groupCohomology.map (alphaSub α N N' hN) (phiCoeff α ρ ρ' hρ N N' hN) 2).hom
      ((groupCohomology.H2π (Rep.of (ρ.comp N.subtype))).hom (bridgeCocycle ρ N z)) = _ at h2
  rw [h2]
  have e : groupCohomology.mapCocycles₂ (alphaSub α N N' hN) (phiCoeff α ρ ρ' hρ N N' hN) (bridgeCocycle ρ N z) =
      bridgeCocycle ρ' N' (phiCocycleN α ρ ρ' hρ N N' hN z) := by
    apply Subtype.ext
    funext p
    change (bridgeCocycle ρ N z : N × N → V) (alphaSub α N N' hN p.1, alphaSub α N N' hN p.2) =
      (bridgeCocycle ρ' N' (phiCocycleN α ρ ρ' hρ N N' hN z) : N' × N' → V) (p.1, p.2)
    rw [bridgeCocycle_apply, bridgeCocycle_apply, phiCocycleN_val]
    refine congrArg z.val.val ?_
    funext i
    fin_cases i <;> simp [alphaSub]
  exact congrArg (groupCohomology.H2π (Rep.of (ρ'.comp N'.subtype))).hom e.symm

end BridgeNat

end TernaryPeriodPolynomials.Argument.EisensteinDual
