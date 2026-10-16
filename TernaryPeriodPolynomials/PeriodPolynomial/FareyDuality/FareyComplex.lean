module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyAction
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.PermProjective

@[expose] public section


/-!
# The augmented chain complex of the dual Farey tree

Formalized by Claude Sonnet 5.5.

Over `ℚ`, with `Γ = GL₂(ℤ)`:

* `P0 = ℚ[Tri]` and `PE = ℚ[OTE]` are the permutation representations on triangles and on oriented edges of the
  dual Farey tree; `P1 ≤ PE` is the subrepresentation of antisymmetric chains (`swap c = -c`).  All three are
  projective (`ofMulAction_projective` for the finite stabilizers of `FareyAction`; `P1` is a retract of `PE` via
  `antiLin`, `inclP1_retrP1`).
* The boundary `d1 : P1 ⟶ P0` is `(t, t') ↦ [t'] - [t]` on antisymmetric chains and `epsMap : P0 ⟶ 1` is the augmentation.
* The complex `0 → P1 → P0 → ℚ → 0` is exact: `d1_injective` (a rank-maximal triangle meets only one edge of an
  antisymmetric cycle, by `rank_P1`), `exists_d1_preimage` (every triangle is joined to the base triangle by a path of
  decreasing rank, `rank_P2`) and `epsMap_surjective`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FareyTree

open CategoryTheory Representation Rep TernaryPoly.RankTwoAugmentedFrames
open scoped MonoidAlgebra Classical
open TernaryPeriodPolynomials.Argument.BinaryDuality (ofMulAction_projective)

/-- The permutation morphism induced by an equivariant map of `GL₂(ℤ)`-sets. -/
def permMap {X Y : Type} [MulAction IntegralGL X] [MulAction IntegralGL Y] (f : X → Y)
    (hf : ∀ (g : IntegralGL) (x : X), f (g • x) = g • f x) :
    Rep.ofMulAction ℚ IntegralGL X ⟶ Rep.ofMulAction ℚ IntegralGL Y :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.ofMulAction ℚ IntegralGL X).ρ) (σ := (Rep.ofMulAction ℚ IntegralGL Y).ρ)
    ((MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ Finsupp.lmapDomain ℚ ℚ f ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
    (fun g v => by
      have key : ((MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ Finsupp.lmapDomain ℚ ℚ f ∘ₗ
          (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) ∘ₗ
            (Representation.ofMulAction ℚ IntegralGL X g) =
          (Representation.ofMulAction ℚ IntegralGL Y g) ∘ₗ
            ((MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ Finsupp.lmapDomain ℚ ℚ f ∘ₗ
              (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) := by
        refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
        simp [Representation.ofMulAction_single, hf]
      exact LinearMap.congr_fun key v))

theorem permMap_single {X Y : Type} [MulAction IntegralGL X] [MulAction IntegralGL Y] (f : X → Y)
    (hf : ∀ (g : IntegralGL) (x : X), f (g • x) = g • f x) (x : X) (r : ℚ) :
    (permMap f hf).hom (MonoidAlgebra.single x r) = MonoidAlgebra.single (f x) r := by
  simp [permMap]

/-- The permutation representation on triangles. -/
abbrev P0 : Rep ℚ IntegralGL := Rep.ofMulAction ℚ IntegralGL Tri

/-- The permutation representation on oriented edges. -/
abbrev PE : Rep ℚ IntegralGL := Rep.ofMulAction ℚ IntegralGL OTE

/-- Source of an oriented edge. -/
def fstMap : PE ⟶ P0 := permMap (fun p : OTE => p.1.1) (fun _ _ => rfl)

/-- Target of an oriented edge. -/
def sndMap : PE ⟶ P0 := permMap (fun p : OTE => p.1.2) (fun _ _ => rfl)

/-- Reversal of oriented edges. -/
def swapMap : PE ⟶ PE := permMap OTE.swap OTE.swap_smul

/-- The boundary `(t, t') ↦ [t'] - [t]` on all oriented edges. -/
def dTilde : PE ⟶ P0 := sndMap - fstMap

/-- The augmentation `[t] ↦ 1`. -/
def epsMap : P0 ⟶ Rep.trivial ℚ IntegralGL ℚ :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := P0.ρ) (σ := (Rep.trivial ℚ IntegralGL ℚ).ρ)
    ((Finsupp.linearCombination ℚ fun _ : Tri => (1 : ℚ)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
    (fun g v => by
      have key : ((Finsupp.linearCombination ℚ fun _ : Tri => (1 : ℚ)) ∘ₗ
          (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) ∘ₗ
            (Representation.ofMulAction ℚ IntegralGL Tri g) =
          ((Finsupp.linearCombination ℚ fun _ : Tri => (1 : ℚ)) ∘ₗ
            (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) := by
        refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
        simp [Representation.ofMulAction_single]
      exact LinearMap.congr_fun key v))

theorem epsMap_single (t : Tri) (r : ℚ) : epsMap.hom (MonoidAlgebra.single t r) = r := by
  change ((Finsupp.linearCombination ℚ fun _ : Tri => (1 : ℚ)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) (MonoidAlgebra.single t r) = r
  simp

theorem fstMap_single (p : OTE) (r : ℚ) :
    fstMap.hom (MonoidAlgebra.single p r) = MonoidAlgebra.single p.1.1 r :=
  permMap_single (fun p : OTE => p.1.1) (fun _ _ => rfl) p r

theorem sndMap_single (p : OTE) (r : ℚ) :
    sndMap.hom (MonoidAlgebra.single p r) = MonoidAlgebra.single p.1.2 r :=
  permMap_single (fun p : OTE => p.1.2) (fun _ _ => rfl) p r

theorem dTilde_hom_apply (v : PE) : dTilde.hom v = sndMap.hom v - fstMap.hom v := rfl

theorem dTilde_single (p : OTE) (r : ℚ) :
    dTilde.hom (MonoidAlgebra.single p r) =
      MonoidAlgebra.single p.1.2 r - MonoidAlgebra.single p.1.1 r := by
  rw [dTilde_hom_apply, sndMap_single, fstMap_single]

theorem swapMap_single (p : OTE) (r : ℚ) :
    swapMap.hom (MonoidAlgebra.single p r) = MonoidAlgebra.single p.swap r :=
  permMap_single OTE.swap OTE.swap_smul p r

theorem eps_dTilde (v : PE) : epsMap.hom (dTilde.hom v) = 0 := by
  have key : epsMap.hom.toLinearMap ∘ₗ dTilde.hom.toLinearMap = 0 := by
    refine MonoidAlgebra.lhom_ext' fun p => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply, LinearMap.zero_apply]
    change epsMap.hom (dTilde.hom (MonoidAlgebra.single p 1)) = 0
    rw [dTilde_single, map_sub, epsMap_single, epsMap_single]; ring
  exact LinearMap.congr_fun key v

theorem swapMap_swapMap (c : PE) : swapMap.hom (swapMap.hom c) = c := by
  have key : swapMap.hom.toLinearMap ∘ₗ swapMap.hom.toLinearMap = LinearMap.id := by
    refine MonoidAlgebra.lhom_ext' fun p => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply, LinearMap.id_apply]
    change swapMap.hom (swapMap.hom (MonoidAlgebra.single p 1)) = MonoidAlgebra.single p 1
    rw [swapMap_single, swapMap_single, OTE.swap_swap]
  exact LinearMap.congr_fun key c

/-- The antisymmetric chains: `swap c = -c`. -/
def antiSub : Submodule ℚ PE := LinearMap.ker (swapMap.hom.toLinearMap + LinearMap.id)

theorem mem_antiSub {c : PE} : c ∈ antiSub ↔ swapMap.hom c + c = 0 := by
  simp [antiSub]

theorem antiSub_invariant (g : IntegralGL) : antiSub ≤ antiSub.comap (PE.ρ g) := by
  intro c hc
  rw [Submodule.mem_comap, mem_antiSub]
  have := Rep.hom_comm_apply swapMap g c
  rw [mem_antiSub] at hc
  change swapMap.hom (PE.ρ g c) + PE.ρ g c = 0
  rw [this, ← map_add, hc, map_zero]

/-- The module of chains of the dual tree: antisymmetric oriented edge chains. -/
abbrev P1 : Rep ℚ IntegralGL := Rep.of (PE.ρ.subrepresentation antiSub antiSub_invariant)

/-- Inclusion of antisymmetric chains. -/
def inclP1 : P1 ⟶ PE :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := P1.ρ) (σ := PE.ρ) antiSub.subtype (fun _ _ => rfl))

/-- The antisymmetrization map `c ↦ (c - swap c) / 2`. -/
def antiLin : PE →ₗ[ℚ] PE := (1 / 2 : ℚ) • (LinearMap.id - swapMap.hom.toLinearMap)

theorem antiLin_apply (c : PE) : antiLin c = (1 / 2 : ℚ) • (c - swapMap.hom c) := rfl

theorem antiLin_mem (c : PE) : antiLin c ∈ antiSub := by
  rw [mem_antiSub, antiLin_apply, map_smul, map_sub, swapMap_swapMap]
  module

/-- The projection onto antisymmetric chains. -/
def retrP1 : PE ⟶ P1 :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := PE.ρ) (σ := P1.ρ)
    (LinearMap.codRestrict antiSub antiLin antiLin_mem)
    (fun g v => by
      apply Subtype.ext
      change antiLin (PE.ρ g v) = PE.ρ g (antiLin v)
      rw [antiLin_apply, antiLin_apply, Rep.hom_comm_apply swapMap g v, map_smul, map_sub]))

theorem inclP1_retrP1 : inclP1 ≫ retrP1 = 𝟙 P1 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change antiLin (c : PE) = c
  have := (mem_antiSub.mp c.2)
  rw [antiLin_apply]
  have h2 : swapMap.hom (c : PE) = -(c : PE) := eq_neg_of_add_eq_zero_left this
  rw [h2]
  module

instance : Projective P0 := ofMulAction_projective (k := ℚ) tri_stabilizer_finite

instance : Projective PE := ofMulAction_projective (k := ℚ) ote_stabilizer_finite

instance : Projective P1 :=
  (⟨inclP1, retrP1, inclP1_retrP1⟩ : Retract P1 PE).projective

/-- The boundary of the dual tree: antisymmetric chains of oriented edges to chains of triangles. -/
def d1 : P1 ⟶ P0 := inclP1 ≫ dTilde

theorem d1_apply (a : P1) : d1.hom a = dTilde.hom (a : PE) := rfl

theorem eps_d1 (a : P1) : epsMap.hom (d1.hom a) = 0 := eps_dTilde _

/-- The oriented edge from `t` to `t'`. -/
def oteOf (t t' : Tri) (h : TAdj t t') : OTE := ⟨(t, t'), h⟩

@[simp] theorem oteOf_fst (t t' : Tri) (h : TAdj t t') : (oteOf t t' h).1.1 = t := rfl

@[simp] theorem oteOf_snd (t t' : Tri) (h : TAdj t t') : (oteOf t t' h).1.2 = t' := rfl

/-- The antisymmetrized basis chain of an oriented edge. -/
def edgeVec (p : OTE) : PE :=
  (1 / 2 : ℚ) • (MonoidAlgebra.single p (1 : ℚ) - MonoidAlgebra.single p.swap (1 : ℚ))

theorem edgeVec_mem (p : OTE) : edgeVec p ∈ antiSub := by
  rw [mem_antiSub]
  unfold edgeVec
  rw [map_smul, map_sub, swapMap_single, swapMap_single, OTE.swap_swap]
  module

theorem dTilde_edgeVec (p : OTE) :
    dTilde.hom (edgeVec p) = MonoidAlgebra.single p.1.2 (1 : ℚ) - MonoidAlgebra.single p.1.1 1 := by
  unfold edgeVec
  rw [map_smul, map_sub, dTilde_single, dTilde_single]
  have : (p.swap).1.2 = p.1.1 := rfl
  have h2 : (p.swap).1.1 = p.1.2 := rfl
  rw [this, h2]
  module

/-- Every triangle differs from the base triangle by a boundary. -/
theorem exists_boundary (t : Tri) :
    ∃ a : P1, d1.hom a = MonoidAlgebra.single t (1 : ℚ) - MonoidAlgebra.single triPlus 1 := by
  induction' hr : triRank t using Nat.strong_induction_on with n ih generalizing t
  by_cases hc : Central t
  · rcases (central_iff t).mp hc with rfl | rfl
    · exact ⟨0, by simp⟩
    · refine ⟨⟨edgeVec (oteOf triPlus triMinus tAdj_triPlus_triMinus), edgeVec_mem _⟩, ?_⟩
      rw [d1_apply]
      exact dTilde_edgeVec _
  · obtain ⟨t', hadj, hlt⟩ := rank_P2 hc
    obtain ⟨a', ha'⟩ := ih (triRank t') (hr ▸ hlt) t' rfl
    refine ⟨a' + ⟨edgeVec (oteOf t' t hadj.symm), edgeVec_mem _⟩, ?_⟩
    rw [map_add, ha', d1_apply]
    change _ + dTilde.hom (edgeVec (oteOf t' t hadj.symm)) = _
    rw [dTilde_edgeVec]
    change _ + (MonoidAlgebra.single t 1 - MonoidAlgebra.single t' 1) = _
    abel

theorem exists_d1_preimage_aux (c : P0) :
    ∃ a : P1, d1.hom a = c - epsMap.hom c • (MonoidAlgebra.single triPlus (1 : ℚ) : P0) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [map_add, ha, hb, map_add, add_smul]
    abel
  | single t r =>
    obtain ⟨a, ha⟩ := exists_boundary t
    refine ⟨r • a, ?_⟩
    rw [map_smul, ha, epsMap_single, smul_sub, MonoidAlgebra.smul_single]
    simp

/-- Exactness at `P₀`: the kernel of the augmentation consists of boundaries. -/
theorem exists_d1_preimage (c : P0) (hc : epsMap.hom c = 0) : ∃ a : P1, d1.hom a = c := by
  obtain ⟨a, ha⟩ := exists_d1_preimage_aux c
  exact ⟨a, by rw [ha, hc]; simp⟩

theorem epsMap_surjective : Function.Surjective epsMap.hom := by
  intro r
  exact ⟨MonoidAlgebra.single triPlus r, epsMap_single _ _⟩

theorem coeff_swapMap (c : PE) (p : OTE) : (swapMap.hom c).coeff p = c.coeff p.swap := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finsupp.add_apply, hx, hy]
  | single q r =>
    rw [swapMap_single, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, Finsupp.single_apply]
    have : (q.swap = p) ↔ (q = p.swap) := by
      constructor
      · rintro rfl; simp
      · rintro rfl; simp
    simp only [this]

theorem coeff_antisymm {c : PE} (hc : c ∈ antiSub) (p : OTE) : c.coeff p.swap = - c.coeff p := by
  have h := congrArg (fun x : PE => x.coeff p) (mem_antiSub.mp hc)
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_swapMap] at h
  simp only [MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at h
  linarith

/-- The `[p.1.1 = t]`-weighted sum of coefficients. -/
def srcSum (t : Tri) (c : PE) : ℚ :=
  c.coeff.sum fun p r => if p.1.1 = t then r else 0

/-- The `[p.1.2 = t]`-weighted sum of coefficients. -/
def tgtSum (t : Tri) (c : PE) : ℚ :=
  c.coeff.sum fun p r => if p.1.2 = t then r else 0

theorem srcSum_add (t : Tri) (x y : PE) : srcSum t (x + y) = srcSum t x + srcSum t y := by
  unfold srcSum
  rw [MonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (by simp) (fun _ _ _ => by split_ifs <;> simp)

theorem tgtSum_add (t : Tri) (x y : PE) : tgtSum t (x + y) = tgtSum t x + tgtSum t y := by
  unfold tgtSum
  rw [MonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (by simp) (fun _ _ _ => by split_ifs <;> simp)

theorem srcSum_single (t : Tri) (p : OTE) (r : ℚ) :
    srcSum t (MonoidAlgebra.single p r) = if p.1.1 = t then r else 0 := by
  unfold srcSum
  rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index]
  simp

theorem tgtSum_single (t : Tri) (p : OTE) (r : ℚ) :
    tgtSum t (MonoidAlgebra.single p r) = if p.1.2 = t then r else 0 := by
  unfold tgtSum
  rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index]
  simp

theorem coeff_dTilde (t : Tri) (c : PE) :
    (dTilde.hom c).coeff t = tgtSum t c - srcSum t c := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp [tgtSum, srcSum]
  | add x y hx hy =>
    rw [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy, tgtSum_add, srcSum_add]; ring
  | single p r =>
    rw [dTilde_single, tgtSum_single, srcSum_single]
    have e : ∀ (x y : P0) (t : Tri), (x - y).coeff t = x.coeff t - y.coeff t := fun _ _ _ => rfl
    rw [e, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single, Finsupp.single_apply,
      Finsupp.single_apply]

theorem tgtSum_eq_srcSum_swap (t : Tri) (c : PE) : tgtSum t c = srcSum t (swapMap.hom c) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp [tgtSum, srcSum]
  | add x y hx hy => rw [map_add, tgtSum_add, srcSum_add, hx, hy]
  | single p r => rw [swapMap_single, tgtSum_single, srcSum_single]; rfl

theorem srcSum_neg (t : Tri) (c : PE) : srcSum t (-c) = - srcSum t c := by
  have := srcSum_add t c (-c)
  rw [add_neg_cancel] at this
  have h0 : srcSum t 0 = 0 := by simp [srcSum]
  linarith

theorem tgtSum_eq_neg_srcSum {c : PE} (hc : c ∈ antiSub) (t : Tri) : tgtSum t c = - srcSum t c := by
  rw [tgtSum_eq_srcSum_swap]
  have : swapMap.hom c = -c := eq_neg_of_add_eq_zero_left (mem_antiSub.mp hc)
  rw [this, srcSum_neg]

theorem srcSum_eq_coeff_of_unique {c : PE} {t : Tri} {p₀ : OTE} (hp₀ : p₀ ∈ c.coeff.support)
    (ht : p₀.1.1 = t)
    (huniq : ∀ q ∈ c.coeff.support, q.1.1 = t → q = p₀) : srcSum t c = c.coeff p₀ := by
  unfold srcSum
  rw [Finsupp.sum, Finset.sum_eq_single p₀]
  · simp [ht]
  · intro q hq hne
    by_cases h : q.1.1 = t
    · exact absurd (huniq q hq h) hne
    · simp [h]
  · intro h; exact absurd hp₀ h

/-- Antisymmetric chains annihilated by the boundary vanish. -/
theorem dTilde_anti_injective {c : PE} (hc : c ∈ antiSub) (h0 : dTilde.hom c = 0) : c = 0 := by
  by_contra hne
  have hsupp : c.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h; apply hne; exact MonoidAlgebra.coeff_eq_zero.mp h
  obtain ⟨p₀, hp₀, hmax⟩ := Finset.exists_max_image c.coeff.support (fun p : OTE => triRank p.1.1) hsupp
  have hsw : ∀ q ∈ c.coeff.support, q.swap ∈ c.coeff.support := by
    intro q hq
    rw [Finsupp.mem_support_iff] at hq ⊢
    rw [coeff_antisymm hc q]; exact neg_ne_zero.mpr hq
  have huniq : ∀ q ∈ c.coeff.support, q.1.1 = p₀.1.1 → q = p₀ := by
    intro q hq hq1
    by_contra hqne
    have hq2 : q.1.2 ≠ p₀.1.2 := by
      intro e
      apply hqne
      exact Subtype.ext (Prod.ext hq1 e)
    have r1 : triRank q.1.2 ≤ triRank p₀.1.1 := by
      have := hmax q.swap (hsw q hq)
      exact this
    have r2 : triRank p₀.1.2 ≤ triRank p₀.1.1 := hmax p₀.swap (hsw p₀ hp₀)
    have a1 : TAdj p₀.1.1 q.1.2 := by rw [← hq1]; exact q.2
    have a2 : TAdj p₀.1.1 p₀.1.2 := p₀.2
    exact rank_P1 a1 a2 hq2 ⟨r1, r2⟩
  have hsrc := srcSum_eq_coeff_of_unique hp₀ rfl huniq
  have hco := coeff_dTilde p₀.1.1 c
  rw [h0, tgtSum_eq_neg_srcSum hc, hsrc] at hco
  have : (0 : P0).coeff p₀.1.1 = 0 := rfl
  rw [this] at hco
  have hne0 : c.coeff p₀ ≠ 0 := Finsupp.mem_support_iff.mp hp₀
  apply hne0
  linarith

theorem d1_injective : Function.Injective d1.hom := by
  intro a b hab
  have h : dTilde.hom ((a - b : P1) : PE) = 0 := by
    rw [← d1_apply, map_sub, hab, sub_self]
  have := dTilde_anti_injective (a - b).2 h
  exact sub_eq_zero.mp (Subtype.ext this)

end TernaryPeriodPolynomials.Argument.FareyTree
