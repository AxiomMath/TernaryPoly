module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.ThreeFactorization

@[expose] public section


/-!
# Away-from-three Hecke operators commute with every Hecke correspondence

For `t` arbitrary write `t = a b` with `a` supported at three and `b` `Good`
(`exists_three_factorization`).  The double cosets `Γ a Γ`, `Γ b Γ` are finite
unions of cosets, so they define correspondences `ta`, `tb`, and
`T t = T ta ∘ T tb` for every realized Hecke action.  An away-from-three `s`
commutes with `ta` (disjoint supports) and with `tb` (Gelfand), hence with `t`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.HeckeCommutativity

/-- The cosets contained in a double coset. -/
def dcosetCosets (g : RationalGL3) : Set (RationalGL3 ⧸ rationalLevel) :=
  {q | ∃ x ∈ dcoset rationalLevel g, (x : RationalGL3 ⧸ rationalLevel) = q}

theorem exists_rep {g : RationalGL3} {q : RationalGL3 ⧸ rationalLevel} (hq : q ∈ dcosetCosets g) :
    ∃ x ∈ dcoset rationalLevel g, (x : RationalGL3 ⧸ rationalLevel) = q := hq

/-- A Hecke correspondence from a finite double coset. -/
def ofFinite (g : RationalGL3) (hfin : (dcosetCosets g).Finite) : HeckeCorrespondence := by
  classical
  exact {
    g := g
    representatives := hfin.toFinset.attach.image
      (fun q => Classical.choose (exists_rep ((Set.Finite.mem_toFinset hfin).mp q.2)))
    inDoubleCoset := by
      intro r hr
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨⟨h₁, hh₁, h₂, hh₂, e⟩, -⟩ :=
        Classical.choose_spec (exists_rep ((Set.Finite.mem_toFinset hfin).mp q.2))
      exact ⟨⟨h₁, hh₁⟩, ⟨h₂, hh₂⟩, e⟩
    complete := by
      intro a b
      have hq : ((a.val * g * b.val : RationalGL3) : RationalGL3 ⧸ rationalLevel) ∈ hfin.toFinset :=
        (Set.Finite.mem_toFinset hfin).mpr ⟨_, ⟨a.val, a.2, b.val, b.2, rfl⟩, rfl⟩
      refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨_, hq⟩), ?_⟩
      have hspec := (Classical.choose_spec (exists_rep ((Set.Finite.mem_toFinset hfin).mp hq))).2
      exact QuotientGroup.eq.mp hspec
    disjoint := by
      intro r hr r' hr' h
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨q', _, rfl⟩ := Finset.mem_image.mp hr'
      have e := (Classical.choose_spec (exists_rep ((Set.Finite.mem_toFinset hfin).mp q.2))).2
      have e' := (Classical.choose_spec (exists_rep ((Set.Finite.mem_toFinset hfin).mp q'.2))).2
      have hqq : q = q' := by
        apply Subtype.ext
        rw [← e, ← e']
        exact QuotientGroup.eq.mpr h
      rw [hqq] }

theorem ofFinite_g (g : RationalGL3) (hfin : (dcosetCosets g).Finite) : (ofFinite g hfin).g = g := rfl

/-- The coset map. -/
abbrev cosetOf : RationalGL3 → RationalGL3 ⧸ rationalLevel := QuotientGroup.mk

/-- The cosets of a correspondence are exactly those of its double coset. -/
theorem image_representatives (t : HeckeCorrespondence) [DecidableEq (RationalGL3 ⧸ rationalLevel)] :
    (t.representatives.image cosetOf : Set _) = dcosetCosets t.g := by
  ext q
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨a, b, e⟩ := t.inDoubleCoset r hr
    exact ⟨r, ⟨a.val, a.2, b.val, b.2, e⟩, rfl⟩
  · rintro ⟨x, ⟨h₁, hh₁, h₂, hh₂, rfl⟩, rfl⟩
    obtain ⟨r, hr, hmem⟩ := t.complete ⟨h₁, hh₁⟩ ⟨h₂, hh₂⟩
    exact ⟨r, hr, QuotientGroup.eq.mpr hmem⟩

theorem dcosetCosets_finite (t : HeckeCorrespondence) : (dcosetCosets t.g).Finite := by
  classical
  rw [← image_representatives t]
  exact Finset.finite_toSet _

/-- Finiteness of a factor's double coset. -/
theorem finite_left_factor {a b : RationalGL3} (hab : DisjointSupport a b)
    (hfin : (dcosetCosets (a * b)).Finite) : (dcosetCosets a).Finite := by
  classical
  let φ : RationalGL3 ⧸ rationalLevel → RationalGL3 ⧸ rationalLevel := fun q =>
    if h : q ∈ dcosetCosets a then
      ((Classical.choose (exists_rep h) * b : RationalGL3) : RationalGL3 ⧸ rationalLevel)
    else q
  apply Set.Finite.of_finite_image (f := φ)
  · apply hfin.subset
    rintro _ ⟨q, hq, rfl⟩
    simp only [φ, dite_eq_left hq]
    exact ⟨_, mul_mem_dcoset_of_disjoint hab (Classical.choose_spec (exists_rep hq)).1
      (self_mem_dcoset _ b), rfl⟩
  · intro q₁ hq₁ q₂ hq₂ h
    simp only [φ, dite_eq_left hq₁, dite_eq_left hq₂] at h
    have hs₁ := Classical.choose_spec (exists_rep hq₁)
    have hs₂ := Classical.choose_spec (exists_rep hq₂)
    have hγ := QuotientGroup.eq.mp h
    set x₁ := Classical.choose (exists_rep hq₁)
    set x₂ := Classical.choose (exists_rep hq₂)
    have hx : x₁⁻¹ * x₂ ∈ rationalLevel := by
      apply inv_mul_mem_of_disjoint hab hs₁.1 hs₂.1 (self_mem_dcoset _ b)
        (mem_dcoset_mul_right _ (self_mem_dcoset _ b) (inv_mem hγ))
      group
    rw [← hs₁.2, ← hs₂.2]
    exact QuotientGroup.eq.mpr hx

theorem finite_right_factor {a b : RationalGL3} (hab : DisjointSupport a b)
    (hfin : (dcosetCosets (a * b)).Finite) : (dcosetCosets b).Finite := by
  classical
  let φ : RationalGL3 ⧸ rationalLevel → RationalGL3 ⧸ rationalLevel := fun q => (a : RationalGL3) • q
  apply Set.Finite.of_finite_image (f := φ)
  · apply hfin.subset
    rintro _ ⟨q, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨a * y, mul_mem_dcoset_of_disjoint hab (self_mem_dcoset _ a) hy, rfl⟩
  · intro q₁ _ q₂ _ h
    simpa [φ] using h

/-- Sums over the cosets of a product of disjointly supported double cosets. -/
theorem sum_factor {V : Type*} [AddCommMonoid V] (F : RationalGL3 → V)
    (hF : ∀ y h, h ∈ rationalLevel → F (y * h) = F y) (t ta tb : HeckeCorrespondence)
    (hab : DisjointSupport ta.g tb.g) (ht : t.g = ta.g * tb.g) :
    ∑ r ∈ t.representatives, F r =
      ∑ x ∈ ta.representatives, ∑ y ∈ tb.representatives, F (x * y) := by
  classical
  let Fb : RationalGL3 ⧸ rationalLevel → V := Quotient.lift (s := QuotientGroup.leftRel rationalLevel) F
    (fun x y hxy => by
      have hxy' : x⁻¹ * y ∈ rationalLevel := QuotientGroup.leftRel_apply.mp hxy
      have := hF x _ hxy'
      rw [mul_inv_cancel_left] at this
      exact this.symm)
  have hFb : ∀ y, F y = Fb (y : RationalGL3 ⧸ rationalLevel) := fun y => rfl
  let mk : RationalGL3 → RationalGL3 ⧸ rationalLevel := cosetOf
  have hinj₁ : Set.InjOn mk t.representatives := by
    intro r hr r' hr' h
    exact t.disjoint r hr r' hr' (QuotientGroup.eq.mp h)
  have hinj₂ : Set.InjOn (fun p : RationalGL3 × RationalGL3 => mk (p.1 * p.2))
      (ta.representatives ×ˢ tb.representatives : Finset _) := by
    rintro ⟨x₁, y₁⟩ hp₁ ⟨x₂, y₂⟩ hp₂ h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp₁ hp₂
    have hγ := QuotientGroup.eq.mp h
    have hrep : ∀ {s : HeckeCorrespondence} {r : RationalGL3}, r ∈ s.representatives →
        r ∈ dcoset rationalLevel s.g := by
      intro s r hr
      obtain ⟨a, b, e⟩ := s.inDoubleCoset r hr
      exact ⟨a.val, a.2, b.val, b.2, e⟩
    have hx : x₁⁻¹ * x₂ ∈ rationalLevel := by
      apply inv_mul_mem_of_disjoint hab (hrep hp₁.1) (hrep hp₂.1) (hrep hp₁.2)
        (mem_dcoset_mul_right _ (hrep hp₂.2) (inv_mem hγ))
      group
    have hxx : x₁ = x₂ := ta.disjoint x₁ hp₁.1 x₂ hp₂.1 hx
    subst hxx
    have hy : y₁⁻¹ * y₂ ∈ rationalLevel := by
      have : y₁⁻¹ * y₂ = (x₁ * y₁)⁻¹ * (x₁ * y₂) := by group
      rw [this]
      exact hγ
    have hyy : y₁ = y₂ := tb.disjoint y₁ hp₁.2 y₂ hp₂.2 hy
    rw [hyy]
  have hL : ∑ r ∈ t.representatives, F r = ∑ q ∈ t.representatives.image mk, Fb q := by
    rw [Finset.sum_image hinj₁]
    rfl
  have hR : ∑ x ∈ ta.representatives, ∑ y ∈ tb.representatives, F (x * y) =
      ∑ q ∈ (ta.representatives ×ˢ tb.representatives).image
        (fun p : RationalGL3 × RationalGL3 => mk (p.1 * p.2)), Fb q := by
    rw [Finset.sum_image hinj₂, Finset.sum_product]
    rfl
  rw [hL, hR]
  congr 1
  apply Finset.coe_injective
  rw [image_representatives t, ht]
  ext q
  simp only [Finset.coe_image, Finset.coe_product, Set.mem_image, Set.mem_prod, Finset.mem_coe]
  constructor
  · rintro ⟨x, ⟨γ, hγ, γ', hγ', rfl⟩, rfl⟩
    obtain ⟨r, hr, hr'⟩ := ta.complete ⟨γ, hγ⟩ 1
    have hδ : r⁻¹ * (γ * ta.g) ∈ rationalLevel := by simpa using hr'
    obtain ⟨r', hr₂, hr₂'⟩ := tb.complete ⟨r⁻¹ * (γ * ta.g), hδ⟩ ⟨γ', hγ'⟩
    refine ⟨(r, r'), ⟨hr, hr₂⟩, ?_⟩
    apply QuotientGroup.eq.mpr
    have : (r * r')⁻¹ * (γ * (ta.g * tb.g) * γ') =
        r'⁻¹ * ((r⁻¹ * (γ * ta.g)) * tb.g * γ') := by group
    rw [this]
    exact hr₂'
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    have hrep : ∀ {s : HeckeCorrespondence} {r : RationalGL3}, r ∈ s.representatives →
        r ∈ dcoset rationalLevel s.g := by
      intro s r hr
      obtain ⟨a, b, e⟩ := s.inDoubleCoset r hr
      exact ⟨a.val, a.2, b.val, b.2, e⟩
    exact ⟨x * y, mul_mem_dcoset_of_disjoint hab (hrep hx) (hrep hy), rfl⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Realized Hecke operators of disjointly supported factors compose. -/
theorem realizesHecke_factor (ρ : Representation ℂ RationalGL3 V)
    (T : HeckeCorrespondence → Module.End ℂ (H2 rationalLevel ρ)) (hT : RealizesHecke ρ T)
    (t ta tb : HeckeCorrespondence) (hab : DisjointSupport ta.g tb.g) (ht : t.g = ta.g * tb.g) :
    T t = T ta * T tb := by
  apply LinearMap.ext
  intro ξ
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ ξ
  obtain ⟨zt, hzt, hTt⟩ := hT t c
  obtain ⟨zb, hzb, hTb⟩ := hT tb c
  obtain ⟨zab, hzab, hTab⟩ := hT ta zb
  change T t (classOf rationalLevel ρ c) = T ta (T tb (classOf rationalLevel ρ c))
  rw [hTt, hTb, hTab]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rw [hzt, hzab]
  let F : RationalGL3 → V := fun y => ρ y (c.val.val (fun i => y⁻¹ * x i))
  have hF : ∀ y h, h ∈ rationalLevel → F (y * h) = F y := by
    intro y h hh
    simp only [F]
    have e : (fun i => (y * h)⁻¹ * x i) = fun i => h⁻¹ * (y⁻¹ * x i) := by
      funext i; group
    rw [e, c.val.property ⟨h⁻¹, inv_mem hh⟩ (fun i => y⁻¹ * x i)]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
  have hL : heckeCochain ρ t c.val x = ∑ r ∈ t.representatives, F r := rfl
  have hR : heckeCochain ρ ta zb.val x =
      ∑ r ∈ ta.representatives, ∑ r' ∈ tb.representatives, F (r * r') := by
    unfold heckeCochain
    apply Finset.sum_congr rfl
    intro r _
    rw [hzb]
    unfold heckeCochain
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro r' _
    simp only [F]
    rw [← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev]
    congr 2
    simp only [mul_assoc]
  rw [hL, hR]
  exact sum_factor F hF t ta tb hab ht

/-- **An away-from-three Hecke operator commutes with every realized Hecke operator.** -/
theorem realizesHecke_comm_all (ρ : Representation ℂ RationalGL3 V)
    (T : HeckeCorrespondence → Module.End ℂ (H2 rationalLevel ρ)) (hT : RealizesHecke ρ T)
    {s : HeckeCorrespondence} (hs : Good s.g) (t : HeckeCorrespondence) :
    T s * T t = T t * T s := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_three_factorization t.g
  have hdisj : DisjointSupport a b := by
    intro v
    by_cases hv : v = placeThree
    · right; rw [hv]; exact locK_three_of_good hb
    · left; exact ha v hv
  have hsa : DisjointSupport s.g a := by
    intro v
    by_cases hv : v = placeThree
    · left; rw [hv]; exact locK_three_of_good hs
    · right; exact ha v hv
  have hfin : (dcosetCosets (a * b)).Finite := by
    rw [← hab]
    exact dcosetCosets_finite t
  let ta := ofFinite a (finite_left_factor hdisj hfin)
  let tb := ofFinite b (finite_right_factor hdisj hfin)
  have hfac : T t = T ta * T tb := realizesHecke_factor ρ T hT t ta tb hdisj hab
  have h1 : T s * T ta = T ta * T s := realizesHecke_comm_of_disjoint ρ T hT hsa
  have h2 : T s * T tb = T tb * T s := realizesHecke_comm ρ T hT hs hb
  rw [hfac, ← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]

/-- The away-from-three pair Hecke operators commute with every pair Hecke operator. -/
theorem pairHecke_comm_all {n : ℕ} (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) {s : HeckeCorrespondence}
    (hs : AwayThree s) (t : HeckeCorrespondence) :
    Commute (pairHecke D hecke s) (pairHecke D hecke t) := by
  have hp : hecke .plane s * hecke .plane t = hecke .plane t * hecke .plane s :=
    realizesHecke_comm_all (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
      (hecke .plane) (hhecke .plane) (good_of_awayThree hs) t
  have hl : hecke .line s * hecke .line t = hecke .line t * hecke .line s :=
    realizesHecke_comm_all (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
      (hecke .line) (hhecke .line) (good_of_awayThree hs) t
  unfold Commute SemiconjBy
  refine LinearMap.ext fun v => ?_
  have ha : hecke .plane s (hecke .plane t v.1) = hecke .plane t (hecke .plane s v.1) := by
    rw [← Module.End.mul_apply, hp, Module.End.mul_apply]
  have hb : hecke .line s (hecke .line t v.2) = hecke .line t (hecke .line s v.2) := by
    rw [← Module.End.mul_apply, hl, Module.End.mul_apply]
  exact Prod.ext ha hb

/-- **Every element of the away-from-three Hecke algebra commutes with every pair Hecke
operator.** -/
theorem awayThreeHeckeAlgebra_commute_pairHecke {n : ℕ} (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    {A : Module.End ℂ (BoundaryCoordinates n D.chi)} (hA : A ∈ awayThreeHeckeAlgebra D hecke)
    (t : HeckeCorrespondence) : Commute A (pairHecke D hecke t) := by
  apply Commute.symm
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hA
  rintro _ ⟨s, hs, rfl⟩
  exact (pairHecke_comm_all D hecke hhecke hs t).symm

end TernaryPeriodPolynomials.HeckeCommutativity
