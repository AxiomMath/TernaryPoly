module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Radical.Restriction

@[expose] public section


/-!
# Surjectivity of the Hochschild-Serre mixed map for a Levi of cohomological dimension one

For a split extension `N ⋊ L` and a representation `E` of `N ⋊ L`, the mixed map sends a
radical-zero two-cycle to a class in `H¹(L, H¹(N, E))`. If every `H²(L, W)` (complex coefficients)
vanishes then this map is **onto**. The proof is explicit. A crossed cocycle of `L` with values in
`H¹(N, E) = Z¹ / B¹` lifts to a crossed cocycle `c̃ : L → Z¹(N, E)`: lift pointwise with a linear
section; the defect is a two-cocycle of `L` with values in `B¹`, hence a coboundary `δa`, and `c̃ = s c + a`.
Then
`z (g₁, g₂) = g₁.left · c̃ (g₁.right) (g₁.right · g₂.left)`
is a radical-zero two-cocycle of `N ⋊ L` whose mixed crossed cochain at `e` is exactly `c̃ e`.
(Compare the paper's use of `H³ = 0` for the Levi, end of Appendix C.2: here the vanishing of
`H²(L, B¹)` replaces the vanishing of `H³(L, E^N)` in the obstruction.)

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

section Lift

/-- Vanishing of degree-two cohomology of the Levi with all complex coefficients. -/
def LeviH2Vanishes (Levi : Type) [Group Levi] : Prop :=
  ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Levi W)
    (x : InhomogeneousH2 ρ), x = 0

/-- **Lifting crossed cocycles through a quotient** when `H²(G, B) = 0`. A crossed cocycle with
values in `Z ⧸ B` lifts to a crossed cocycle with values in `Z`. -/
theorem lift_crossed_of_vanishing {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ G Z) (B : Submodule ℂ Z) (hB : ∀ g, B ≤ B.comap (ρ g))
    (hG : LeviH2Vanishes G) (c : crossedCocycles (ρ.quotient B hB)) :
    ∃ ct : crossedCocycles ρ, ∀ l, B.mkQ (ct.val l) = c.val l := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective B.mkQ (Submodule.range_mkQ B)
  have hsπ : ∀ x, B.mkQ (s x) = x := fun x => LinearMap.congr_fun hs x
  have hπρ : ∀ (g : G) (x : Z), ρ.quotient B hB g (B.mkQ x) = B.mkQ (ρ g x) :=
    fun g x => rfl
  let f : G → Z := fun l => s (c.val l)
  let d : G → G → Z := fun g h => f (g * h) - f g - ρ g (f h)
  have hd : ∀ g h, d g h ∈ B := by
    intro g h
    refine (Submodule.Quotient.mk_eq_zero B).mp ?_
    change B.mkQ (f (g * h) - f g - ρ g (f h)) = 0
    rw [map_sub, map_sub, ← hπρ]
    simp only [f, hsπ]
    rw [c.property g h]
    abel
  let ρB : Representation ℂ G B := Representation.subrepresentation ρ B hB
  let b : G → G → B := fun g h => ⟨d g h, hd g h⟩
  have hcyc : b ∈ inhomogeneousTwoCycles ρB := by
    intro g h k
    apply Subtype.ext
    change ρ g (d h k) - d (g * h) k + d g (h * k) - d g h = 0
    simp only [d, map_sub, map_mul, Module.End.mul_apply, mul_assoc]
    abel
  have zero := hG ρB ((inhomogeneousBoundaries ρB).mkQ ⟨b, hcyc⟩)
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp zero
  have ha' : ∀ g h, ρ g (a h : Z) - (a (g * h) : Z) + (a g : Z) = d g h := by
    intro g h
    exact congrArg (fun q : inhomogeneousTwoCycles ρB => (q.val g h : Z)) ha
  refine ⟨⟨fun l => f l + (a l : Z), ?_⟩, ?_⟩
  · intro g h
    have := ha' g h
    change f (g * h) + (a (g * h) : Z) = (f g + (a g : Z)) + ρ g (f h + (a h : Z))
    have hdef : f (g * h) = f g + ρ g (f h) + d g h := by
      simp only [d]
      abel
    rw [hdef, map_add, ← this]
    abel
  · intro l
    change B.mkQ (f l + (a l : Z)) = c.val l
    have h0 : B.mkQ (a l : Z) = 0 := (Submodule.Quotient.mk_eq_zero B).mpr (a l).property
    rw [map_add, h0, add_zero]
    exact hsπ _

end Lift

section Realize

variable {Radical Levi Value : Type} [Group Radical] [Group Levi]
  [AddCommGroup Value] [Module ℂ Value]
  (action : Levi →* MulAut Radical)
  (representation : Representation ℂ (SemidirectProduct Radical Levi action) Value)
  (ct : crossedCocycles (leviCrossedRepresentation action representation))

/-- The two-cochain of `N ⋊ L` attached to a crossed cocycle `ct : L → Z¹(N, E)`:
`z (g₁, g₂) = g₁.left · ct (g₁.right) (g₁.right · g₂.left)`. -/
def liftCochain (g₁ g₂ : SemidirectProduct Radical Levi action) : Value :=
  representation (SemidirectProduct.inl g₁.left)
    ((ct.val g₁.right).val (action g₁.right g₂.left))

theorem ct_cross (l₁ l₂ : Levi) (r : Radical) :
    (ct.val (l₁ * l₂)).val r = (ct.val l₁).val r +
      representation (SemidirectProduct.inr l₁) ((ct.val l₂).val (action l₁⁻¹ r)) := by
  have := congrArg (fun x => x.val r) (ct.property l₁ l₂)
  exact this

theorem ct_rad (l : Levi) (m m' : Radical) :
    (ct.val l).val (m * m') = (ct.val l).val m +
      representation (SemidirectProduct.inl m) ((ct.val l).val m') :=
  (ct.val l).property m m'

theorem ct_one (r : Radical) : (ct.val 1).val r = 0 := by
  have h := ct_cross action representation ct 1 1 r
  rw [mul_one] at h
  simp only [inv_one, map_one, MulAut.one_apply, map_one, Module.End.one_apply] at h
  exact left_eq_add.mp h |>.symm ▸ rfl

theorem inr_mul_inl (l : Levi) (n : Radical) :
    (SemidirectProduct.inr l : SemidirectProduct Radical Levi action) * SemidirectProduct.inl n =
      SemidirectProduct.inl (action l n) * SemidirectProduct.inr l := by
  have := semidirect_conjugation_intertwines action l (action l n)
  simpa using this

theorem rep_decomp (g : SemidirectProduct Radical Levi action) (v : Value) :
    representation g v = representation (SemidirectProduct.inl g.left)
      (representation (SemidirectProduct.inr g.right) v) := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
  rw [map_mul, Module.End.mul_apply]

theorem liftCochain_cocycle :
    liftCochain action representation ct ∈ inhomogeneousTwoCycles representation := by
  intro g₁ g₂ g₃
  obtain ⟨n₁, l₁⟩ := g₁
  obtain ⟨n₂, l₂⟩ := g₂
  obtain ⟨n₃, l₃⟩ := g₃
  have hmul : ∀ (a b : SemidirectProduct Radical Levi action),
      (a * b).left = a.left * action a.right b.left ∧ (a * b).right = a.right * b.right :=
    fun a b => ⟨rfl, rfl⟩
  simp only [liftCochain, hmul]
  -- notation
  set m₂ : Radical := action l₁ n₂ with hm₂
  set u : Radical := action (l₁ * l₂) n₃ with hu
  have hact : action l₁ (n₂ * action l₂ n₃) = m₂ * u := by
    rw [map_mul]
    simp [hm₂, hu]
  have hinv : action l₁⁻¹ u = action l₂ n₃ := by
    simp [hu]
  have h1 := ct_cross action representation ct l₁ l₂ u
  rw [hinv] at h1
  have h2 := ct_rad action representation ct l₁ m₂ u
  have hconj : representation (SemidirectProduct.inr l₁)
        (representation (SemidirectProduct.inl n₂) (((ct.val l₂).val) (action l₂ n₃))) =
      representation (SemidirectProduct.inl m₂)
        (representation (SemidirectProduct.inr l₁) (((ct.val l₂).val) (action l₂ n₃))) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      inr_mul_inl]
  rw [hact, rep_decomp action representation ⟨n₁, l₁⟩]
  simp only [map_mul, Module.End.mul_apply]
  rw [h2, h1, hconj]
  simp only [map_add]
  abel

/-- The radical-zero two-cycle attached to `ct`. -/
def liftCycle : radicalZeroTwoCycles action representation :=
  ⟨⟨liftCochain action representation ct, liftCochain_cocycle action representation ct⟩,
    by
      intro r s
      simp only [liftCochain, SemidirectProduct.right_inl, ct_one, map_zero]⟩

theorem mixedCrossedCochain_liftCycle (e : Levi) (r : Radical) :
    mixedCrossedCochain action representation (liftCycle action representation ct) e r =
      (ct.val e).val r := by
  change liftCochain action representation ct (SemidirectProduct.inr e)
      (SemidirectProduct.inl (action e⁻¹ r)) -
    liftCochain action representation ct (SemidirectProduct.inl r) (SemidirectProduct.inr e) = _
  simp only [liftCochain, SemidirectProduct.left_inr, SemidirectProduct.right_inr,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, ct_one, map_zero, sub_zero]
  simp

theorem mixedH1CocycleMap_liftCycle (e : Levi) :
    (mixedH1CocycleMap action representation (liftCycle action representation ct)).val e =
      (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ (ct.val e) := by
  change (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
      (mixedCrossedMap action representation e (liftCycle action representation ct)) = _
  congr 1
  apply Subtype.ext
  funext r
  exact mixedCrossedCochain_liftCycle action representation ct e r

end Realize

/-- **Surjectivity of the Hochschild-Serre mixed map** for a split extension whose Levi has
vanishing complex `H²`: every class of `H¹(L, H¹(N, E))` is the mixed class of a radical-zero
two-cocycle. -/
theorem radicalKernelMixedMap_surjective {Radical Levi Value : Type} [Group Radical] [Group Levi]
    [AddCommGroup Value] [Module ℂ Value] (action : Levi →* MulAut Radical)
    (representation : Representation ℂ (SemidirectProduct Radical Levi action) Value)
    (hL : LeviH2Vanishes Levi) :
    Function.Surjective (radicalKernelMixedMap action representation) := by
  intro y
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨ct, hct⟩ := lift_crossed_of_vanishing (leviCrossedRepresentation action representation)
    (crossedBoundaries (representation.comp SemidirectProduct.inl))
    (leviCrossed_boundaries_stable action representation) hL c
  refine ⟨radicalZeroH2ToKernel action representation
    ((radicalZeroBoundaries action representation).mkQ (liftCycle action representation ct)), ?_⟩
  rw [radicalKernelMixedMap_representative]
  have hmix : mixedH1CocycleMap action representation (liftCycle action representation ct) = c := by
    apply Subtype.ext
    funext e
    rw [mixedH1CocycleMap_liftCycle]
    exact hct e
  rw [hmix]
  rfl

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
