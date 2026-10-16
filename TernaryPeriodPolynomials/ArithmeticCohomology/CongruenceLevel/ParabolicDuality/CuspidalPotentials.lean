module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspidalCriterion

@[expose] public section


/-!
# Cusp potentials: the Farey differential is injective on normalized twisted cusp functions

Formalized by Claude Sonnet 5.5.  Context: `ar:eq:facepair`.

* `cusp_const`: the Farey graph is connected, so a function on cusps with `Ψ(head q) = Ψ(tail q)` for all oriented dual edges is constant;
* `Tn A`: the twisted cusp functions vanishing at `cusp₁`; `bdryTw` is injective on `Tn A` (`bdryTw_injOn`);
* `mTw`: the class in `H¹(Γ(N), A)` of the cocycle `fTw Φ (γ) = Φ(γ cusp₁) - γ Φ(cusp₁)` of a twisted cusp function; it is cuspidal
  (`mTw_mem_cuspidal`), every cuspidal class is of this form (`exists_Tn_of_cuspidal`), and `mTw Φ = 0` exactly for
  `Φ = Ψ - Ψ(cusp₁)` with `Ψ` strictly equivariant (`ker_mTw`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open scoped Classical

section Connected

theorem mem_triangle_cusps (g : IntegralGL) {x : RationalLine2} (hx : x ∈ (g • triPlus).1) :
    x = g • cusp1 ∨ x = g • cusp2 ∨ x = g • cusp3 := by
  rw [mem_tri_smul, mem_triPlus_cusps] at hx
  rcases hx with h | h | h
  · left; rw [← h, smul_inv_smul]
  · right; left; rw [← h, smul_inv_smul]
  · right; right; rw [← h, smul_inv_smul]

theorem tri_vertices_eq {M : Type} {Ψ : RationalLine2 → M} (h : ∀ q : OTE, Ψ (head q) = Ψ (tail q)) (t : Tri)
    {x y : RationalLine2} (hx : x ∈ t.1) (hy : y ∈ t.1) : Ψ x = Ψ y := by
  obtain ⟨g, hg, rfl⟩ := tri_transitive_sl t
  have e12 : Ψ (g • cusp2) = Ψ (g • cusp1) := by
    have := h (g • p0)
    rwa [head_eq hg rfl, tail_eq hg rfl] at this
  have e23 : Ψ (g • cusp3) = Ψ (g • cusp2) := by
    have := h ((g * rho) • p0)
    rwa [head_eq (hg.mul rho_det) rfl, tail_eq (hg.mul rho_det) rfl, mul_smul, mul_smul, rho_c2, rho_c1] at this
  have key : ∀ z ∈ (g • triPlus).1, Ψ z = Ψ (g • cusp1) := by
    intro z hz
    rcases mem_triangle_cusps g hz with rfl | rfl | rfl
    · rfl
    · exact e12
    · exact e23.trans e12
  rw [key x hx, key y hy]

/-- **The Farey graph is connected**: a function on the cusps that is constant along every Farey edge is constant. -/
theorem cusp_const {M : Type} {Ψ : RationalLine2 → M} (h : ∀ q : OTE, Ψ (head q) = Ψ (tail q)) (x : RationalLine2) :
    Ψ x = Ψ cusp1 := by
  have key : ∀ t : Tri, Relation.ReflTransGen TAdj triPlus t → ∀ z ∈ t.1, Ψ z = Ψ cusp1 := by
    intro t ht
    induction ht with
    | refl => intro z hz; exact tri_vertices_eq h triPlus hz (by simp [triPlus])
    | @tail b c _ hadj ih =>
      intro z hz
      obtain ⟨-, x', y', -, hx, -, hx', -⟩ := hadj
      rw [tri_vertices_eq h c hz hx', ih x' hx]
  obtain ⟨g, -, hg⟩ := exists_sl_cusp x
  exact key (g • triPlus) (tri_reach _) x (by rw [← hg]; exact smul_mem_tri_smul (by simp [triPlus]))

end Connected


section TwistedCusp

variable {N : ℕ}

/-- The crossed homomorphism of a twisted cusp function, read at the base cusp. -/
def fTw (A : Rep ℂ (gammaNGL N)) (Φ : RationalLine2 → A) (γ : gammaNGL N) : A :=
  Φ ((γ : IntegralGL) • cusp1) - A.ρ γ (Φ cusp1)

theorem fTw_eq {A : Rep ℂ (gammaNGL N)} {Φ : RationalLine2 → A} {f : gammaNGL N → A}
    (hΦ : ∀ (γ : gammaNGL N) (x : RationalLine2), Φ (γ • x) = A.ρ γ (Φ x) + f γ) : fTw A Φ = f := by
  funext γ
  unfold fTw
  have := hΦ γ cusp1
  change Φ ((γ : IntegralGL) • cusp1) = _ at this
  rw [this]; abel

theorem fTw_twisted (A : Rep ℂ (gammaNGL N)) {Φ : RationalLine2 → A} (hΦ : Φ ∈ Tw A.ρ) (γ : gammaNGL N)
    (x : RationalLine2) : Φ ((γ : IntegralGL) • x) = A.ρ γ (Φ x) + fTw A Φ γ := by
  obtain ⟨f, -, hf⟩ := hΦ
  rw [fTw_eq hf]
  exact hf γ x

theorem fTw_cocycle (A : Rep ℂ (gammaNGL N)) {Φ : RationalLine2 → A} (hΦ : Φ ∈ Tw A.ρ) :
    ∀ g h, fTw A Φ (g * h) = A.ρ g (fTw A Φ h) + fTw A Φ g := by
  obtain ⟨f, hf, hf'⟩ := hΦ
  rw [fTw_eq hf']
  exact hf

/-- `fTw` as a linear map on twisted cusp functions. -/
def fTwL (A : Rep ℂ (gammaNGL N)) : Tw A.ρ →ₗ[ℂ] (gammaNGL N → A) where
  toFun Φ := fTw A Φ.1
  map_add' Φ Ψ := by
    funext γ
    simp only [fTw, Submodule.coe_add, Pi.add_apply, map_add]
    abel
  map_smul' c Φ := by
    funext γ
    simp only [fTw, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply]

theorem fTwL_mem (A : Rep ℂ (gammaNGL N)) (Φ : Tw A.ρ) : fTwL A Φ ∈ groupCohomology.cocycles₁ A :=
  (groupCohomology.mem_cocycles₁_iff _).2 (fTw_cocycle A Φ.2)

/-- The class in `H¹(Γ(N), A)` of a twisted cusp function. -/
def mTw (A : Rep ℂ (gammaNGL N)) : Tw A.ρ →ₗ[ℂ] groupCohomology.H1 A :=
  (groupCohomology.H1π A).hom.comp (LinearMap.codRestrict _ (fTwL A) (fTwL_mem A))

theorem mTw_apply (A : Rep ℂ (gammaNGL N)) (Φ : Tw A.ρ) :
    mTw A Φ = groupCohomology.H1π A ⟨fTw A Φ.1, fTwL_mem A Φ⟩ := rfl

/-- The class of a twisted cusp function is cuspidal. -/
theorem mTw_mem_cuspidal (A : Rep ℂ (gammaNGL N)) (Φ : Tw A.ρ) : mTw A Φ ∈ cuspidalSub A := by
  rw [mTw_apply, mem_cuspidalSub_π]
  intro x
  refine ⟨-Φ.1 x, fun γ hγ => ?_⟩
  have h := fTw_twisted A Φ.2 γ x
  change Φ.1 ((γ : IntegralGL) • x) = _ at h
  have hx : (γ : IntegralGL) • x = x := hγ
  rw [hx] at h
  change fTw A Φ.1 γ = A.ρ γ (-Φ.1 x) - -Φ.1 x
  rw [map_neg]
  have : fTw A Φ.1 γ = Φ.1 x - A.ρ γ (Φ.1 x) := by
    rw [eq_sub_iff_add_eq, add_comm]; exact h.symm
  rw [this]; abel

/-- Shifting a strictly equivariant function by a constant gives a twisted cusp function. -/
theorem shift_mem_Tw (A : Rep ℂ (gammaNGL N)) {Ψ : RationalLine2 → A} (hΨ : Ψ ∈ EqFn (gammaNGL N) RationalLine2 A.ρ) (k : A) :
    (fun x => Ψ x - k) ∈ Tw A.ρ := by
  refine ⟨fun γ => A.ρ γ k - k, fun g h => ?_, fun γ x => ?_⟩
  · simp only [map_mul, Module.End.mul_apply, map_sub]; abel
  · simp only [hΨ γ x, map_sub]; abel

theorem fTw_shift (A : Rep ℂ (gammaNGL N)) {Ψ : RationalLine2 → A} (hΨ : Ψ ∈ EqFn (gammaNGL N) RationalLine2 A.ρ) (k : A) :
    fTw A (fun x => Ψ x - k) = fun γ => A.ρ γ k - k := by
  funext γ
  unfold fTw
  have h1 := hΨ γ cusp1
  change Ψ ((γ : IntegralGL) • cusp1) = _ at h1
  simp only [h1, map_sub]; abel

theorem mTw_shift (A : Rep ℂ (gammaNGL N)) {Ψ : RationalLine2 → A} (hΨ : Ψ ∈ EqFn (gammaNGL N) RationalLine2 A.ρ) (k : A) :
    mTw A ⟨fun x => Ψ x - k, shift_mem_Tw A hΨ k⟩ = 0 := by
  rw [mTw_apply, groupCohomology.H1π_eq_zero_iff]
  refine ⟨k, ?_⟩
  funext γ
  simp only [groupCohomology.d₀₁_hom_apply]
  exact (congrFun (fTw_shift A hΨ k) γ).symm

/-- Every class killed by `mTw` on a normalized twisted function comes from a strictly equivariant function. -/
theorem ker_mTw (A : Rep ℂ (gammaNGL N)) (Φ : Tw A.ρ) (h0 : Φ.1 cusp1 = 0) (hm : mTw A Φ = 0) :
    ∃ Ψ : RationalLine2 → A, Ψ ∈ EqFn (gammaNGL N) RationalLine2 A.ρ ∧ ∀ x, Φ.1 x = Ψ x - Ψ cusp1 := by
  rw [mTw_apply, groupCohomology.H1π_eq_zero_iff] at hm
  obtain ⟨u, hu⟩ := hm
  have hu' : ∀ γ, fTw A Φ.1 γ = A.ρ γ u - u := fun γ => by
    have := congrFun hu γ
    simp only [groupCohomology.d₀₁_hom_apply] at this
    exact this.symm
  refine ⟨fun x => Φ.1 x + u, ?_, fun x => ?_⟩
  · intro γ x
    change Φ.1 ((γ : IntegralGL) • x) + u = A.ρ γ (Φ.1 x + u)
    rw [fTw_twisted A Φ.2 γ x, hu' γ, map_add]; abel
  · simp [h0]


/-- **Every cuspidal class is the class of a normalized twisted cusp function.** -/
theorem exists_Tn_of_cuspidal (hN : 3 ≤ N) (A : Rep ℂ (gammaNGL N)) {x : groupCohomology.H1 A} (hx : x ∈ cuspidalSub A) :
    ∃ Φ : Tw A.ρ, Φ.1 cusp1 = 0 ∧ mTw A Φ = x := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    rw [mem_cuspidalSub_π] at hx
    have hf : ∀ g h, c.1 (g * h) = A.ρ g (c.1 h) + c.1 g := (groupCohomology.mem_cocycles₁_iff c.1).1 c.2
    obtain ⟨Φ, hΦ⟩ := exists_twisted A.ρ (cuspReps hN) c.1 hf (fun r _ => by
      obtain ⟨u, hu⟩ := hx r
      exact ⟨u, hu⟩)
    set u₀ := Φ cusp1 with hu₀
    have hmem : (fun x => Φ x - u₀) ∈ Tw A.ρ := by
      refine ⟨fun g => c.1 g + A.ρ g u₀ - u₀, fun g h => ?_, fun γ x => ?_⟩
      · simp only [hf, map_mul, Module.End.mul_apply, map_add, map_sub]; abel
      · simp only [hΦ, map_sub]; abel
    refine ⟨⟨_, hmem⟩, by simp [hu₀], ?_⟩
    rw [mTw_apply, groupCohomology.H1π_eq_iff]
    refine ⟨u₀, ?_⟩
    funext γ
    simp only [groupCohomology.d₀₁_hom_apply]
    change A.ρ γ u₀ - u₀ = fTw A (fun x => Φ x - u₀) γ - c.1 γ
    unfold fTw
    have := hΦ γ cusp1
    change Φ ((γ : IntegralGL) • cusp1) = _ at this
    simp only [this, map_sub]
    abel

/-- The Farey differential is injective on normalized twisted cusp functions (the Farey graph is connected). -/
theorem bdryTw_injOn (hN : 3 ≤ N) (A : Rep ℂ (gammaNGL N)) {Φ : Tw A.ρ} (h0 : Φ.1 cusp1 = 0)
    (hb : bdryTw A.ρ hN Φ = 0) : Φ = 0 := by
  apply Subtype.ext
  funext x
  have hq : ∀ q : OTE, Φ.1 (head q) = Φ.1 (tail q) := fun q => by
    have := congrFun (congrArg Subtype.val hb) q
    change Φ.1 (head q) - Φ.1 (tail q) = 0 at this
    exact sub_eq_zero.mp this
  rw [cusp_const hq x, h0]
  rfl

theorem bdryTw_shift (hN : 3 ≤ N) (A : Rep ℂ (gammaNGL N)) {Ψ : RationalLine2 → A}
    (hΨ : Ψ ∈ EqFn (gammaNGL N) RationalLine2 A.ρ) (k : A) :
    bdryTw A.ρ hN ⟨fun x => Ψ x - k, shift_mem_Tw A hΨ k⟩ = bdryTw A.ρ hN ⟨Ψ, eqFn_le_Tw A.ρ hΨ⟩ := by
  apply Subtype.ext
  funext q
  change (Ψ (head q) - k) - (Ψ (tail q) - k) = Ψ (head q) - Ψ (tail q)
  abel

end TwistedCusp

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
