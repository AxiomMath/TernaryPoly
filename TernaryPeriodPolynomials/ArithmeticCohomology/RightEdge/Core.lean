module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Surjective

@[expose] public section


open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

/-!
# The Hochschild-Serre right edge for a split extension `N ⋊ L` with `H²(L, ·) = 0`: the cochain-level theorem

Formalized by Claude Sonnet 5.5.

Paper: (`0 → H¹(L_R, H¹(N_R, E)) → H²(R, E) → H²(N_R, E)^{L_R} → 0` for `R = N_R ⋊ L_R`, "because `L_R` has rational cohomological dimension one").
The proof avoids spectral sequences and `H³`: it shifts dimension through the right-translation module
`U = Map(R, V) ⊇ V`, which is `N`-acyclic in degrees one and two, so that the right edge in degree two for `V` becomes the right edge in degree ONE for `U/V`, where the obstruction
lies in `H²(L, (U/V)^N) = 0`.

* `H2Vanishes`: vanishing of the complex degree-two cohomology of `L` in elementary form; `h2Vanishes_of_leviH2Vanishes`;
* `lift_crossed`: the degree-one right edge: an `L`-invariant crossed homomorphism `c : N → W` is the restriction of a crossed homomorphism `C : R → W` (`W` any `R`-module);
* `ShiftData`: an `R`-module `U ⊇ V` acyclic for `N` in degrees one and two; `right_edge_cochain`: for any such data, an `L`-invariant two-cocycle `z` of `N` is, up to a
  coboundary, the restriction of a two-cocycle of `R`;
* `mapShiftData`: the data for `U = Map(R, V)` with `(r·f)(x) = f(x r)` and `ι v = (x ↦ ρ(x) v)` (no hypothesis on `N`, `L`, `V`);
* `right_edge_cochain_map`: the conclusion with no module left.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RightEdge

open TernaryPeriodPolynomials.Argument.FacePairingFull.Face (LeviH2Vanishes)

/-- Vanishing of the complex degree-two cohomology of a group, in elementary form: every inhomogeneous two-cocycle with values in a complex representation is a coboundary. -/
def H2Vanishes (L : Type) [Group L] : Prop :=
  ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρW : Representation ℂ L W) (b : L → L → W),
    (∀ g h k, ρW g (b h k) - b (g * h) k + b g (h * k) - b g h = 0) →
    ∃ a : L → W, ∀ g h, ρW g (a h) - a (g * h) + a g = b g h

theorem h2Vanishes_of_leviH2Vanishes {L : Type} [Group L] (hL : LeviH2Vanishes L) : H2Vanishes L := by
  intro W _ _ ρW b hb
  have hcyc : b ∈ inhomogeneousTwoCycles ρW := hb
  have zero := hL ρW ((inhomogeneousBoundaries ρW).mkQ ⟨b, hcyc⟩)
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp zero
  exact ⟨a, fun g h => congrArg (fun q : inhomogeneousTwoCycles ρW => q.val g h) ha⟩

section Semidirect

variable {N L : Type} [Group N] [Group L] (φ : L →* MulAut N)

/-- `φ_{(l₁ l₂)⁻¹} = φ_{l₂}⁻¹ φ_{l₁}⁻¹`. -/
theorem phi_inv_mul (l₁ l₂ : L) (a : N) : (φ (l₁ * l₂))⁻¹ a = (φ l₂)⁻¹ ((φ l₁)⁻¹ a) := by
  rw [map_mul, mul_inv_rev]
  rfl

end Semidirect


section Lift

variable {N L W : Type} [Group N] [Group L] [AddCommGroup W] [Module ℂ W] (φ : L →* MulAut N)
  (ρ : Representation ℂ (N ⋊[φ] L) W)

theorem conj_rel (l : L) (a : N) (w : W) :
    ρ (SemidirectProduct.inr l) (ρ (SemidirectProduct.inl a) w) =
      ρ (SemidirectProduct.inl (φ l a)) (ρ (SemidirectProduct.inr l) w) := by
  have h : (SemidirectProduct.inl (φ l a) : N ⋊[φ] L) * SemidirectProduct.inr l =
      SemidirectProduct.inr l * SemidirectProduct.inl a := by
    rw [SemidirectProduct.inl_aut, mul_assoc (SemidirectProduct.inr l * SemidirectProduct.inl a),
      ← map_mul, inv_mul_cancel, map_one, mul_one]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, h]

theorem conj_rel' (l : L) (a : N) (w : W) :
    ρ (SemidirectProduct.inl a) (ρ (SemidirectProduct.inr l) w) =
      ρ (SemidirectProduct.inr l) (ρ (SemidirectProduct.inl ((φ l)⁻¹ a)) w) := by
  rw [conj_rel φ ρ l ((φ l)⁻¹ a) w]
  have e : φ l ((φ l)⁻¹ a) = a := by
    rw [show (φ l) ((φ l)⁻¹ a) = ((φ l) * (φ l)⁻¹) a from rfl, mul_inv_cancel]
    rfl
  rw [e]

/-- The `N`-fixed vectors of an `R`-module. -/
def fixN : Submodule ℂ W where
  carrier := {w | ∀ a : N, ρ (SemidirectProduct.inl a) w = w}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy a
    simp only [map_add, hx a, hy a]
  smul_mem' := by
    intro c x hx a
    simp only [map_smul, hx a]

theorem fixN_stable (l : L) (w : W) (hw : w ∈ fixN φ ρ) : ρ (SemidirectProduct.inr l) w ∈ fixN φ ρ := by
  intro a
  rw [conj_rel' φ ρ l a w, hw]


open SemidirectProduct in
/-- **Lifting an `L`-invariant crossed homomorphism of the radical to the semidirect product** (the degree-one right edge, `H²(L, W^N) = 0`). -/
theorem lift_crossed (hL : H2Vanishes L) (c : N → W)
    (hc : ∀ a b, c (a * b) = c a + ρ (inl a) (c b))
    (hinv : ∀ l : L, ∃ w : W, ∀ a : N, ρ (inr l) (c ((φ l)⁻¹ a)) - c a = ρ (inl a) w - w) :
    ∃ C : N ⋊[φ] L → W, (∀ r s, C (r * s) = C r + ρ r (C s)) ∧ ∀ a, C (inl a) = c a := by
  choose w hw using hinv
  have e1 : ∀ l a, ρ (inl a) (w l) = w l + ρ (inr l) (c ((φ l)⁻¹ a)) - c a := by
    intro l a
    have := hw l a
    linear_combination (norm := abel) -this
  have hmulL : ∀ l₁ l₂ (x : W), ρ (inr (l₁ * l₂)) x = ρ (inr l₁) (ρ (inr l₂) x) := by
    intro l₁ l₂ x
    rw [map_mul, map_mul]
    rfl
  let θ : L → L → W := fun l₁ l₂ => ρ (inr l₁) (w l₂) - w (l₁ * l₂) + w l₁
  have hθfix : ∀ l₁ l₂, θ l₁ l₂ ∈ fixN φ ρ := by
    intro l₁ l₂ a
    change ρ (inl a) (ρ (inr l₁) (w l₂) - w (l₁ * l₂) + w l₁) = ρ (inr l₁) (w l₂) - w (l₁ * l₂) + w l₁
    rw [map_add, map_sub, conj_rel' φ ρ l₁ a, e1 l₂ ((φ l₁)⁻¹ a), e1 (l₁ * l₂) a, e1 l₁ a, phi_inv_mul φ l₁ l₂ a,
      hmulL l₁ l₂, map_sub, map_add]
    abel
  let ρFix : Representation ℂ L (fixN φ ρ) :=
    Representation.subrepresentation (ρ.comp inr : Representation ℂ L W) (fixN φ ρ) (fun g x hx => fixN_stable φ ρ g x hx)
  have hρFix : ∀ g (x : fixN φ ρ), ((ρFix g x : fixN φ ρ) : W) = ρ (inr g) x.1 := fun g x => rfl
  let θ' : L → L → fixN φ ρ := fun l₁ l₂ => ⟨θ l₁ l₂, hθfix l₁ l₂⟩
  have hcyc : ∀ g h k, ρFix g (θ' h k) - θ' (g * h) k + θ' g (h * k) - θ' g h = 0 := by
    intro g h k
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_zero, hρFix]
    change ρ (inr g) (ρ (inr h) (w k) - w (h * k) + w h) - (ρ (inr (g * h)) (w k) - w (g * h * k) + w (g * h)) +
      (ρ (inr g) (w (h * k)) - w (g * (h * k)) + w g) - (ρ (inr g) (w h) - w (g * h) + w g) = 0
    rw [hmulL g h, mul_assoc g h k]
    simp only [map_add, map_sub]
    abel
  obtain ⟨κ, hκ⟩ := hL ρFix θ' hcyc
  let u : L → W := fun l => w l - (κ l).1
  have hucr : ∀ g h, u (g * h) = u g + ρ (inr g) (u h) := by
    intro g h
    have := congrArg Subtype.val (hκ g h)
    simp only [Submodule.coe_sub, Submodule.coe_add, hρFix] at this
    change ρ (inr g) (κ h).1 - (κ (g * h)).1 + (κ g).1 = ρ (inr g) (w h) - w (g * h) + w g at this
    change w (g * h) - (κ (g * h)).1 = (w g - (κ g).1) + ρ (inr g) (w h - (κ h).1)
    rw [map_sub]
    linear_combination (norm := abel) this
  have hu : ∀ l a, ρ (inr l) (c ((φ l)⁻¹ a)) - c a = ρ (inl a) (u l) - u l := by
    intro l a
    change _ = ρ (inl a) (w l - (κ l).1) - (w l - (κ l).1)
    rw [map_sub, (κ l).2 a, hw l a]
    abel
  have hu1 : u 1 = 0 := by
    have := hucr 1 1
    simp only [mul_one, map_one, Module.End.one_apply] at this
    have h2 : u 1 + u 1 = u 1 + 0 := by rw [← this]; simp
    exact add_left_cancel h2
  refine ⟨fun r => c r.left + ρ (inl r.left) (u r.right), ?_, ?_⟩
  · intro r s
    have hρr : ∀ x, ρ r x = ρ (inl r.left) (ρ (inr r.right) x) := by
      intro x
      conv_lhs => rw [← inl_left_mul_inr_right r]
      rw [map_mul]
      rfl
    have a2eq : (φ r.right)⁻¹ (φ r.right s.left) = s.left := by
      rw [show (φ r.right)⁻¹ (φ r.right s.left) = ((φ r.right)⁻¹ * (φ r.right)) s.left from rfl, inv_mul_cancel]
      rfl
    have hm := hu r.right (φ r.right s.left)
    rw [a2eq] at hm
    have hconj := conj_rel φ ρ r.right s.left (u s.right)
    change c (r.left * φ r.right s.left) + ρ (inl (r.left * φ r.right s.left)) (u (r.right * s.right)) =
      (c r.left + ρ (inl r.left) (u r.right)) + ρ r (c s.left + ρ (inl s.left) (u s.right))
    have hm' : ρ (inr r.right) (c s.left) = c (φ r.right s.left) + ρ (inl (φ r.right s.left)) (u r.right) - u r.right := by
      linear_combination (norm := abel) hm
    rw [hc, hucr, hρr, map_add, map_add, hconj, hm']
    simp only [map_mul, Module.End.mul_apply, map_add, map_sub]
    abel
  · intro a
    change c a + ρ (inl a) (u 1) = c a
    rw [hu1, map_zero, add_zero]

end Lift


section Shift

variable {N L V : Type} [Group N] [Group L] [AddCommGroup V] [Module ℂ V] (φ : L →* MulAut N)
  (ρ : Representation ℂ (N ⋊[φ] L) V)

open SemidirectProduct

/-- The data of a dimension-shifting module for the right edge: an `R`-module `U` containing `V` which is acyclic for `N` in degrees one and two. -/
structure ShiftData (U : Type) [AddCommGroup U] [Module ℂ U] where
  ρU : Representation ℂ (N ⋊[φ] L) U
  ι : V →ₗ[ℂ] U
  ι_inj : Function.Injective ι
  ι_equiv : ∀ r v, ρU r (ι v) = ι (ρ r v)
  acyc1 : ∀ ξ : N → U, (∀ a b, ξ (a * b) = ξ a + ρU (inl a) (ξ b)) →
    ∃ u : U, ∀ a, ξ a = ρU (inl a) u - u
  acyc2 : ∀ z : N → N → V, (∀ a b c, ρ (inl a) (z b c) - z (a * b) c + z a (b * c) - z a b = 0) →
    ∃ ξ : N → U, ∀ a b, ρU (inl a) (ξ b) - ξ (a * b) + ξ a = ι (z a b)

/-- **The right edge at the level of cochains.**  Let `R = N ⋊ L` with `H²(L, ·) = 0`, `ρ` a representation of `R`, and `z` a two-cocycle of `N` with values in `ρ|_N`
whose class is `L`-invariant (`l·z − z = δη_l`, `(l·z)(a,b) = ρ(l) z(l⁻¹ a l, l⁻¹ b l)`).  Then `z` is the restriction, up to a coboundary, of a two-cocycle of `R`. -/
theorem right_edge_cochain {U : Type} [AddCommGroup U] [Module ℂ U] (S : ShiftData φ ρ U) (hL : H2Vanishes L)
    (z : N → N → V) (hz : ∀ a b c, ρ (inl a) (z b c) - z (a * b) c + z a (b * c) - z a b = 0)
    (hinv : ∀ l : L, ∃ η : N → V, ∀ a b, ρ (inr l) (z ((φ l)⁻¹ a) ((φ l)⁻¹ b)) - z a b =
      ρ (inl a) (η b) - η (a * b) + η a) :
    ∃ (Z : N ⋊[φ] L → N ⋊[φ] L → V) (ζ : N → V),
      (∀ a b c, ρ a (Z b c) - Z (a * b) c + Z a (b * c) - Z a b = 0) ∧
      ∀ a b, Z (inl a) (inl b) = z a b + (ρ (inl a) (ζ b) - ζ (a * b) + ζ a) := by
  obtain ⟨ξ, hξ⟩ := S.acyc2 z hz
  let B : Submodule ℂ U := LinearMap.range S.ι
  have hB : ∀ r, B ≤ B.comap (S.ρU r) := by
    rintro r _ ⟨v, rfl⟩
    exact ⟨ρ r v, (S.ι_equiv r v).symm⟩
  let ρ' : Representation ℂ (N ⋊[φ] L) (U ⧸ B) := S.ρU.quotient B hB
  have hρ' : ∀ r u, ρ' r (B.mkQ u) = B.mkQ (S.ρU r u) := fun r u => rfl
  have hmk : ∀ v, B.mkQ (S.ι v) = 0 := fun v => (Submodule.Quotient.mk_eq_zero B).mpr ⟨v, rfl⟩
  let x : N → U ⧸ B := fun a => B.mkQ (ξ a)
  have hxcr : ∀ a b, x (a * b) = x a + ρ' (inl a) (x b) := by
    intro a b
    have := hξ a b
    have h0 : B.mkQ (S.ρU (inl a) (ξ b) - ξ (a * b) + ξ a) = 0 := by rw [this]; exact hmk _
    rw [map_add, map_sub] at h0
    change B.mkQ (ξ (a * b)) = B.mkQ (ξ a) + B.mkQ (S.ρU (inl a) (ξ b))
    linear_combination (norm := abel) -h0
  have hxinv : ∀ l : L, ∃ w : U ⧸ B, ∀ a : N,
      ρ' (inr l) (x ((φ l)⁻¹ a)) - x a = ρ' (inl a) w - w := by
    intro l
    obtain ⟨η, hη⟩ := hinv l
    let ψ : N → U := fun a => S.ρU (inr l) (ξ ((φ l)⁻¹ a)) - ξ a - S.ι (η a)
    have hψ : ∀ a b, ψ (a * b) = ψ a + S.ρU (inl a) (ψ b) := by
      intro a b
      have h1 := hξ a b
      have h2 := congrArg (S.ρU (inr l)) (hξ ((φ l)⁻¹ a) ((φ l)⁻¹ b))
      simp only [map_add, map_sub] at h2
      have h3 := congrArg S.ι (hη a b)
      simp only [map_add, map_sub] at h3
      rw [← S.ι_equiv, ← S.ι_equiv] at h3
      have hconj := conj_rel' φ S.ρU l a (ξ ((φ l)⁻¹ b))
      have hab : (φ l)⁻¹ (a * b) = (φ l)⁻¹ a * (φ l)⁻¹ b := map_mul _ _ _
      change S.ρU (inr l) (ξ ((φ l)⁻¹ (a * b))) - ξ (a * b) - S.ι (η (a * b)) =
        (S.ρU (inr l) (ξ ((φ l)⁻¹ a)) - ξ a - S.ι (η a)) +
          S.ρU (inl a) (S.ρU (inr l) (ξ ((φ l)⁻¹ b)) - ξ b - S.ι (η b))
      rw [hab, map_sub, map_sub, hconj]
      linear_combination (norm := abel) h1 - h2 - h3
    obtain ⟨u, hu⟩ := S.acyc1 ψ hψ
    refine ⟨B.mkQ u, fun a => ?_⟩
    have := congrArg B.mkQ (hu a)
    rw [map_sub, map_sub, map_sub] at this
    change B.mkQ (S.ρU (inr l) (ξ ((φ l)⁻¹ a))) - B.mkQ (ξ a) - B.mkQ (S.ι (η a)) = _ at this
    rw [hmk, sub_zero] at this
    exact this
  obtain ⟨C, hC, hCinl⟩ := lift_crossed φ ρ' hL x hxcr hxinv
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective B.mkQ (Submodule.range_mkQ B)
  have hsπ : ∀ y, B.mkQ (s y) = y := fun y => LinearMap.congr_fun hs y
  let Ξ : N ⋊[φ] L → U := fun r => s (C r)
  have hdΞ : ∀ a b, S.ρU a (Ξ b) - Ξ (a * b) + Ξ a ∈ B := by
    intro a b
    rw [← Submodule.Quotient.mk_eq_zero]
    change B.mkQ (S.ρU a (Ξ b) - Ξ (a * b) + Ξ a) = 0
    have e1 : B.mkQ (S.ρU a (Ξ b)) = ρ' a (C b) := by
      rw [← hρ']
      exact congrArg (ρ' a) (hsπ (C b))
    rw [map_add, map_sub, e1]
    change ρ' a (C b) - B.mkQ (s (C (a * b))) + B.mkQ (s (C a)) = 0
    rw [hsπ, hsπ, hC a b]
    abel
  choose Z hZ using fun a b => hdΞ a b
  have hZ' : ∀ a b, S.ι (Z a b) = S.ρU a (Ξ b) - Ξ (a * b) + Ξ a := hZ
  have hΞinl : ∀ a : N, ∃ v : V, S.ι v = Ξ (inl a) - ξ a := by
    intro a
    have : Ξ (inl a) - ξ a ∈ B := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change B.mkQ (s (C (inl a)) - ξ a) = 0
      rw [map_sub, hsπ, hCinl a]
      exact sub_self _
    exact this
  choose ζ hζ using hΞinl
  refine ⟨Z, ζ, ?_, ?_⟩
  · intro a b c
    apply S.ι_inj
    simp only [map_add, map_sub, map_zero]
    rw [← S.ι_equiv a (Z b c), hZ' b c, hZ' (a * b) c, hZ' a (b * c), hZ' a b]
    simp only [map_add, map_sub, map_mul, Module.End.mul_apply, mul_assoc]
    abel
  · intro a b
    apply S.ι_inj
    have hA : ∀ t : N, Ξ (inl t) = ξ t + S.ι (ζ t) := fun t => by rw [hζ t]; abel
    rw [hZ', ← map_mul, hA, hA, hA]
    simp only [map_add, map_sub]
    rw [← S.ι_equiv (inl a) (ζ b)]
    have := hξ a b
    linear_combination (norm := abel) this


/-! ### The dimension-shifting module `Map(R, V)` -/

section MapModel

open SemidirectProduct

variable {N L V : Type} [Group N] [Group L] [AddCommGroup V] [Module ℂ V] (φ : L →* MulAut N)
  (ρ : Representation ℂ (N ⋊[φ] L) V)

/-- The `L`-part of an element of `N ⋊ L`. -/
def lpart (x : N ⋊[φ] L) : L := x.right

/-- The `N`-part of the decomposition `x = l · n`, `l ∈ L`, `n ∈ N`. -/
def npart (x : N ⋊[φ] L) : N := (φ x.right)⁻¹ x.left

theorem decomp (x : N ⋊[φ] L) : inr (lpart φ x) * inl (npart φ x) = x := by
  apply SemidirectProduct.ext
  · change (1 : N) * (φ x.right) ((φ x.right)⁻¹ x.left) = x.left
    rw [one_mul]
    exact (show (φ x.right) ((φ x.right)⁻¹ x.left) = ((φ x.right) * (φ x.right)⁻¹) x.left from rfl).trans
      (by rw [mul_inv_cancel]; rfl)
  · change x.right * 1 = x.right
    rw [mul_one]

theorem lpart_mk (l : L) (n : N) : lpart φ (inr l * inl n : N ⋊[φ] L) = l := by
  change l * 1 = l
  rw [mul_one]

theorem npart_mk (l : L) (n : N) : npart φ (inr l * inl n : N ⋊[φ] L) = n := by
  change (φ (l * 1))⁻¹ ((1 : N) * φ l n) = n
  rw [mul_one, one_mul]
  exact (show (φ l)⁻¹ (φ l n) = ((φ l)⁻¹ * (φ l)) n from rfl).trans (by rw [inv_mul_cancel]; rfl)

theorem lpart_mul_inl (x : N ⋊[φ] L) (m : N) : lpart φ (x * inl m) = lpart φ x := by
  conv_lhs => rw [← decomp φ x, mul_assoc, ← map_mul]
  exact lpart_mk φ _ _

theorem npart_mul_inl (x : N ⋊[φ] L) (m : N) : npart φ (x * inl m) = npart φ x * m := by
  conv_lhs => rw [← decomp φ x, mul_assoc, ← map_mul]
  exact npart_mk φ _ _

/-- The right-translation representation on `Map(R, V)`: `(r · f)(x) = f(x r)`. -/
def mapRep : Representation ℂ (N ⋊[φ] L) ((N ⋊[φ] L) → V) where
  toFun r := LinearMap.funLeft ℂ V (fun x => x * r)
  map_one' := by
    ext f x
    simp
  map_mul' r s := by
    ext f x
    simp [mul_assoc]

theorem mapRep_apply (r : N ⋊[φ] L) (f : (N ⋊[φ] L) → V) (x : N ⋊[φ] L) : mapRep φ r f x = f (x * r) := rfl

/-- The embedding `V → Map(R, V)`, `v ↦ (x ↦ ρ(x) v)`. -/
def mapIota : V →ₗ[ℂ] ((N ⋊[φ] L) → V) where
  toFun v := fun x => ρ x v
  map_add' v w := by funext x; simp
  map_smul' c v := by funext x; simp

theorem mapIota_apply (v : V) (x : N ⋊[φ] L) : mapIota φ ρ v x = ρ x v := rfl


/-- **The dimension-shifting data** `V ↪ Map(R, V)`: the right-translation module is acyclic for `N` in degrees one and two. -/
def mapShiftData : ShiftData φ ρ ((N ⋊[φ] L) → V) where
  ρU := mapRep φ
  ι := mapIota φ ρ
  ι_inj := by
    intro v w h
    have := congrFun h 1
    simpa [mapIota_apply] using this
  ι_equiv := by
    intro r v
    funext x
    change ρ (x * r) v = ρ x (ρ r v)
    rw [map_mul]
    rfl
  acyc1 := by
    intro ξ hξ
    refine ⟨fun x => ξ (npart φ x) (inr (lpart φ x)), fun a => ?_⟩
    funext x
    change ξ a x = ξ (npart φ (x * inl a)) (inr (lpart φ (x * inl a))) - ξ (npart φ x) (inr (lpart φ x))
    rw [npart_mul_inl, lpart_mul_inl]
    have h1 : ξ (npart φ x * a) (inr (lpart φ x)) = ξ (npart φ x) (inr (lpart φ x)) + ξ a x := by
      rw [hξ (npart φ x) a]
      change _ + ξ a (inr (lpart φ x) * inl (npart φ x)) = _
      rw [decomp]
    rw [h1]
    abel
  acyc2 := by
    intro z hz
    refine ⟨fun a x => ρ (inr (lpart φ x)) (z (npart φ x) a), fun a b => ?_⟩
    funext x
    change ρ (inr (lpart φ (x * inl a))) (z (npart φ (x * inl a)) b) -
        ρ (inr (lpart φ x)) (z (npart φ x) (a * b)) + ρ (inr (lpart φ x)) (z (npart φ x) a) = ρ x (z a b)
    rw [npart_mul_inl, lpart_mul_inl]
    have hx : ρ x (z a b) = ρ (inr (lpart φ x)) (ρ (inl (npart φ x)) (z a b)) := by
      conv_lhs => rw [← decomp φ x]
      rw [map_mul]
      rfl
    rw [hx]
    have := hz (npart φ x) a b
    rw [← map_sub, ← map_add]
    refine congrArg (ρ (inr (lpart φ x))) ?_
    linear_combination (norm := abel) -this


/-- **The right edge at the level of cochains** (no module left): an `L`-invariant two-cocycle of `N` with values in `ρ|_N` extends, up to a coboundary of `N`, to a
two-cocycle of `R = N ⋊ L` with values in `ρ`, whenever `H²(L, ·)` vanishes. -/
theorem right_edge_cochain_map (hL : H2Vanishes L)
    (z : N → N → V) (hz : ∀ a b c, ρ (inl a) (z b c) - z (a * b) c + z a (b * c) - z a b = 0)
    (hinv : ∀ l : L, ∃ η : N → V, ∀ a b, ρ (inr l) (z ((φ l)⁻¹ a) ((φ l)⁻¹ b)) - z a b =
      ρ (inl a) (η b) - η (a * b) + η a) :
    ∃ (Z : N ⋊[φ] L → N ⋊[φ] L → V) (ζ : N → V),
      (∀ a b c, ρ a (Z b c) - Z (a * b) c + Z a (b * c) - Z a b = 0) ∧
      ∀ a b, Z (inl a) (inl b) = z a b + (ρ (inl a) (ζ b) - ζ (a * b) + ζ a) :=
  right_edge_cochain φ ρ (mapShiftData φ ρ) hL z hz hinv

end MapModel

end Shift

end TernaryPeriodPolynomials.Argument.RightEdge
