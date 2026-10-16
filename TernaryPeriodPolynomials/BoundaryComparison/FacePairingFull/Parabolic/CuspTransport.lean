module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Mixed.Restriction

@[expose] public section


/-!
# Vanishing of crossed classes on subgroups, and its transport

For a crossed cocycle `x` of a group `G` with values in a representation `V`, the restriction of
its class to a subgroup `S` vanishes iff `x s = s w - w` on `S` for one `w`
(`vanishesOn_mk_iff`). Conjugating the subgroup moves the primitive: if `x` vanishes on `S` and
`g t g⁻¹ ∈ S` for all `t ∈ T`, then `x` vanishes on `T` with primitive `g⁻¹ (w + x g)`
(`trivialOn_conj`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The class of `x` restricts to zero on the subgroup `S`. -/
theorem vanishesOn_mk_iff (S : Subgroup G) (x : crossedCocycles ρ) :
    crossedPullbackH1 S.subtype ρ ((crossedBoundaries ρ).mkQ x) = 0 ↔
      ∃ w : V, ∀ s ∈ S, x.val s = ρ s w - w := by
  rw [crossedPullbackH1_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, fun s hs => ?_⟩
    have := congrArg (fun y : crossedCocycles (ρ.comp S.subtype) => y.val ⟨s, hs⟩) hw
    exact this.symm
  · rintro ⟨w, hw⟩
    refine ⟨w, Subtype.ext (funext fun s => ?_)⟩
    exact (hw s.val s.property).symm

/-- The pullback of the class of `x` along a homomorphism `φ` vanishes iff `x ∘ φ` has a primitive. -/
theorem pullback_mk_eq_zero_iff {S : Type} [Group S] (φ : S →* G) (x : crossedCocycles ρ) :
    crossedPullbackH1 φ ρ ((crossedBoundaries ρ).mkQ x) = 0 ↔
      ∃ w : V, ∀ s, x.val (φ s) = ρ (φ s) w - w := by
  rw [crossedPullbackH1_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, fun s => ?_⟩
    have := congrArg (fun y : crossedCocycles (ρ.comp φ) => y.val s) hw
    exact this.symm
  · rintro ⟨w, hw⟩
    exact ⟨w, Subtype.ext (funext fun s => (hw s).symm)⟩

/-- `x` is a coboundary on the set `S`, with one primitive. -/
def TrivialOn (x : G → V) (S : Set G) : Prop := ∃ w : V, ∀ s ∈ S, x s = ρ s w - w

theorem crossed_one (x : crossedCocycles ρ) : x.val 1 = 0 := by
  have h := x.property 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  exact left_eq_add.mp h

theorem crossed_inv (x : crossedCocycles ρ) (g : G) :
    x.val g⁻¹ = -(ρ g⁻¹ (x.val g)) := by
  have h := x.property g g⁻¹
  rw [mul_inv_cancel, crossed_one] at h
  have h2 := congrArg (ρ g⁻¹) h.symm
  rw [map_zero, map_add, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] at h2
  exact eq_neg_of_add_eq_zero_right h2

/-- Transport of vanishing along conjugation. -/
theorem trivialOn_conj (x : crossedCocycles ρ) (g : G) (S T : Set G)
    (hS : TrivialOn ρ x.val S) (hT : ∀ t ∈ T, g * t * g⁻¹ ∈ S) : TrivialOn ρ x.val T := by
  obtain ⟨w', hw'⟩ := hS
  refine ⟨ρ g⁻¹ (w' + x.val g), fun t ht => ?_⟩
  have key := hw' _ (hT t ht)
  have e : t = g⁻¹ * ((g * t * g⁻¹) * g) := by group
  have hρ : ∀ v, ρ t (ρ g⁻¹ v) = ρ g⁻¹ (ρ (g * t * g⁻¹) v) := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 1
    group
  have ht : x.val t = x.val g⁻¹ + ρ g⁻¹ (x.val (g * t * g⁻¹) + ρ (g * t * g⁻¹) (x.val g)) := by
    conv_lhs => rw [e]
    rw [x.property g⁻¹ _, x.property (g * t * g⁻¹) g]
  rw [ht, crossed_inv, key, map_add, hρ]
  simp only [map_add, map_sub]
  abel

theorem rep_zpow_fixed (T : G) (v : V) (hv : ρ T v = v) (k : ℤ) : ρ (T ^ k) v = v := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, map_mul, Module.End.mul_apply, hv, ih]
  | pred k ih =>
    have hinv : ρ T⁻¹ v = v := by
      have := congrArg (ρ T⁻¹) hv
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
      exact this.symm
    rw [zpow_sub_one, map_mul, Module.End.mul_apply, hinv, ih]

theorem crossed_zpow_zero (z : crossedCocycles ρ) (T : G) (hz : z.val T = 0) (k : ℤ) :
    z.val (T ^ k) = 0 := by
  induction k using Int.induction_on with
  | zero => simpa using crossed_one ρ z
  | succ k ih =>
    rw [zpow_add_one, z.property, hz, ih, map_zero, add_zero]
  | pred k ih =>
    have h := z.property (T ^ (-(k : ℤ) - 1)) T
    rw [← zpow_add_one, sub_add_cancel, hz, map_zero, add_zero] at h
    rw [← h, ih]

/-- **A cocycle trivial on `T` is trivial on `⟨T, ε⟩`** when `ε` is an involution inverting `T`:
the primitive is corrected by half the value at `ε`. -/
theorem cusp_group_trivial (x : crossedCocycles ρ) (T ε : G) (hεε : ε * ε = 1)
    (hcomm : ε * T = T⁻¹ * ε) (u : V) (hu : x.val T = ρ T u - u) :
    ∃ w : V, (∀ k : ℤ, x.val (T ^ k) = ρ (T ^ k) w - w) ∧
      (∀ k : ℤ, x.val (ε * T ^ k) = ρ (ε * T ^ k) w - w) := by
  set z : crossedCocycles ρ := x - crossedBoundary ρ u with hzdef
  have hzval : ∀ g, z.val g = x.val g - (ρ g u - u) := fun g => rfl
  have hzT : z.val T = 0 := by rw [hzval, hu, sub_self]
  have hzpow := crossed_zpow_zero ρ z T hzT
  -- the value at ε is fixed by T
  have hfix : ρ T (z.val ε) = z.val ε := by
    have h1 := z.property ε T
    have h2 := z.property T⁻¹ ε
    rw [hcomm] at h1
    rw [hzT, map_zero, add_zero] at h1
    have hzinv : z.val T⁻¹ = 0 := by simpa using hzpow (-1)
    rw [hzinv, zero_add] at h2
    have h3 : ρ T (ρ T⁻¹ (z.val ε)) = ρ T (z.val ε) := by rw [← h2, h1]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h3
    exact h3.symm
  have hanti : ρ ε (z.val ε) = -(z.val ε) := by
    have h := z.property ε ε
    rw [hεε, crossed_one] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  set w₀ : V := (-(1 / 2 : ℂ)) • z.val ε with hw₀
  have hTw : ρ T w₀ = w₀ := by rw [hw₀, map_smul, hfix]
  have hεw : ρ ε w₀ - w₀ = z.val ε := by
    rw [hw₀, map_smul, hanti]
    module
  refine ⟨u + w₀, fun k => ?_, fun k => ?_⟩
  · have h1 : x.val (T ^ k) = z.val (T ^ k) + (ρ (T ^ k) u - u) := by rw [hzval]; abel
    rw [h1, hzpow, map_add, rep_zpow_fixed ρ T w₀ hTw]
    abel
  · have h1 : x.val (ε * T ^ k) = z.val (ε * T ^ k) + (ρ (ε * T ^ k) u - u) := by
      rw [hzval]; abel
    have h2 : z.val (ε * T ^ k) = z.val ε := by
      rw [z.property, hzpow, map_zero, add_zero]
    rw [h1, h2]
    simp only [map_add, map_mul, Module.End.mul_apply, rep_zpow_fixed ρ T w₀ hTw]
    rw [← hεw]
    abel

/-- A cocycle trivial on `T` is trivial on `⟨T⟩ × (Z/2)²`, for commuting involutions `m` (commuting
with `T`) and `ε` (inverting `T`). -/
theorem klein_cusp_trivial (x : crossedCocycles ρ) (T m ε : G) (hmm : m * m = 1) (hεε : ε * ε = 1)
    (hmε : m * ε = ε * m) (hmT : m * T = T * m) (hεT : ε * T = T⁻¹ * ε) (u : V)
    (hu : x.val T = ρ T u - u) :
    ∃ w : V, ∀ k : ℤ,
      x.val (T ^ k) = ρ (T ^ k) w - w ∧ x.val (m * T ^ k) = ρ (m * T ^ k) w - w ∧
        x.val (ε * T ^ k) = ρ (ε * T ^ k) w - w ∧
        x.val (m * ε * T ^ k) = ρ (m * ε * T ^ k) w - w := by
  set z : crossedCocycles ρ := x - crossedBoundary ρ u with hzdef
  have hzval : ∀ g, z.val g = x.val g - (ρ g u - u) := fun g => rfl
  have hzT : z.val T = 0 := by rw [hzval, hu, sub_self]
  have hzpow := crossed_zpow_zero ρ z T hzT
  have hzinv : z.val T⁻¹ = 0 := by simpa using hzpow (-1)
  have hρρ : ∀ (g h : G) (v : V), ρ g (ρ h v) = ρ (g * h) v := by
    intro g h v
    rw [map_mul, Module.End.mul_apply]
  set a := z.val m with ha
  set b := z.val ε with hb
  set c := z.val (m * ε) with hc
  -- involution relations
  have hma : ρ m a = -a := by
    have h := z.property m m
    rw [hmm, crossed_one] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hεb : ρ ε b = -b := by
    have h := z.property ε ε
    rw [hεε, crossed_one] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hc1 : c = a + ρ m b := z.property m ε
  have hc2 : c = b + ρ ε a := by
    have h := z.property ε m
    rw [← hmε] at h
    exact h
  -- fixedness under T
  have hTa : ρ T a = a := by
    have h1 := z.property m T
    have h2 := z.property T m
    rw [hmT, hzT, map_zero, add_zero] at h1
    rw [hzT, zero_add] at h2
    exact (h2.symm.trans h1)
  have hTb : ρ T b = b := by
    have h1 := z.property ε T
    have h2 := z.property T⁻¹ ε
    rw [hεT, hzT, map_zero, add_zero] at h1
    rw [hzinv, zero_add] at h2
    have h3 : ρ T (ρ T⁻¹ b) = ρ T b := by rw [← h2, h1]
    rw [hρρ, mul_inv_cancel, map_one, Module.End.one_apply] at h3
    exact h3.symm
  have hTc : ρ T c = c := by
    rw [hc1, map_add, hTa]
    congr 1
    rw [hρρ, ← hmT, ← hρρ, hTb]
  -- action of the involutions
  have hmb : ρ m b = c - a := by rw [hc1]; abel
  have hmm' : ∀ v, ρ m (ρ m v) = v := by
    intro v; rw [hρρ, hmm, map_one, Module.End.one_apply]
  have hεε' : ∀ v, ρ ε (ρ ε v) = v := by
    intro v; rw [hρρ, hεε, map_one, Module.End.one_apply]
  have hmc : ρ m c = b - a := by
    rw [hc1, map_add, hma, hmm']; abel
  have hεa : ρ ε a = c - b := by rw [hc2]; abel
  have hεc : ρ ε c = a - b := by
    rw [hc2, map_add, hεb, hεε']; abel
  set w₀ : V := (-(1 / 4 : ℂ)) • (a + b + c) with hw₀
  have hTw : ρ T w₀ = w₀ := by
    rw [hw₀, map_smul, map_add, map_add, hTa, hTb, hTc]
  have hmw : ρ m w₀ - w₀ = a := by
    rw [hw₀, map_smul, map_add, map_add, hma, hmb, hmc]
    module
  have hεw : ρ ε w₀ - w₀ = b := by
    rw [hw₀, map_smul, map_add, map_add, hεa, hεb, hεc]
    module
  have hmεw : ρ (m * ε) w₀ - w₀ = c := by
    rw [← hρρ]
    simp only [hw₀, map_smul, map_add, map_sub, map_neg, hεa, hεb, hεc, hma, hmb, hmc]
    module
  have hfix : ∀ (k : ℤ), ρ (T ^ k) w₀ = w₀ := fun k => rep_zpow_fixed ρ T w₀ hTw k
  refine ⟨u + w₀, fun k => ⟨?_, ?_, ?_, ?_⟩⟩
  · have h1 : x.val (T ^ k) = z.val (T ^ k) + (ρ (T ^ k) u - u) := by rw [hzval]; abel
    rw [h1, hzpow, map_add, hfix]; abel
  · have h1 : x.val (m * T ^ k) = z.val (m * T ^ k) + (ρ (m * T ^ k) u - u) := by
      rw [hzval]; abel
    have h2 : z.val (m * T ^ k) = a := by rw [z.property, hzpow, map_zero, add_zero]
    rw [h1, h2]
    simp only [map_add, map_mul, Module.End.mul_apply, hfix]
    rw [← hmw]; abel
  · have h1 : x.val (ε * T ^ k) = z.val (ε * T ^ k) + (ρ (ε * T ^ k) u - u) := by
      rw [hzval]; abel
    have h2 : z.val (ε * T ^ k) = b := by rw [z.property, hzpow, map_zero, add_zero]
    rw [h1, h2]
    simp only [map_add, map_mul, Module.End.mul_apply, hfix]
    rw [← hεw]; abel
  · have h1 : x.val (m * ε * T ^ k) = z.val (m * ε * T ^ k) + (ρ (m * ε * T ^ k) u - u) := by
      rw [hzval]; abel
    have h2 : z.val (m * ε * T ^ k) = c := by rw [z.property, hzpow, map_zero, add_zero]
    rw [h1, h2]
    simp only [map_add, map_mul, Module.End.mul_apply, hfix]
    rw [← hmεw, map_mul, Module.End.mul_apply]; abel

end TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic
