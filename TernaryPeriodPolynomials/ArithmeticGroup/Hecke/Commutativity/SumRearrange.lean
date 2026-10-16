module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.ShimuraCount
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section


/-!
# Rearranging double Hecke sums

For finite sets of left-coset representatives `R` of `HaH/H` and `S` of `HbH/H`,
the number of pairs `(r, s) ∈ R × S` with `rsH = cH` is the Hecke structure constant
`m(a, b; c)`.  When the structure constants are symmetric (Gelfand's trick) every
right-`H`-invariant function `F` satisfies
`∑_{r,s} F (r s) = ∑_{s,r} F (s r)`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

namespace TernaryPeriodPolynomials.HeckeCommutativity

variable {G : Type*} [Group G] (H : Subgroup G)

/-- `R` is a complete irredundant set of representatives of `HaH/H`. -/
def IsReps (R : Finset G) (a : G) : Prop :=
  (∀ r ∈ R, r ∈ dcoset H a) ∧ (∀ y ∈ dcoset H a, ∃ r ∈ R, r⁻¹ * y ∈ H) ∧
    ∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ H → r = r'

theorem card_filter_eq_heckeCount [DecidableEq (G ⧸ H)] {R S : Finset G} {a b : G}
    (hR : IsReps H R a) (hS : IsReps H S b) (c : G) :
    ((R ×ˢ S).filter (fun p => ((p.1 * p.2 : G) : G ⧸ H) = (c : G ⧸ H))).card =
      heckeCount H a b c := by
  unfold heckeCount
  rw [← Nat.card_eq_finsetCard]
  symm
  apply Nat.card_congr
  symm
  let T := (R ×ˢ S).filter (fun p => ((p.1 * p.2 : G) : G ⧸ H) = (c : G ⧸ H))
  have hmem : ∀ p : T, ((p.1.1 : G) : G ⧸ H) ∈ cosetSet H a b c := by
    intro p
    have hp := p.2
    simp only [T, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hr, hs⟩, hq⟩ := hp
    rw [mem_cosetSet_iff]
    refine ⟨hR.1 _ hr, ?_⟩
    have h1 : (p.1.1 * p.1.2)⁻¹ * c ∈ H := QuotientGroup.eq.mp hq
    have : p.1.1⁻¹ * c = p.1.2 * ((p.1.1 * p.1.2)⁻¹ * c) := by group
    rw [this]
    exact mem_dcoset_mul_right H (hS.1 _ hs) h1
  refine Equiv.ofBijective (fun p => ⟨_, hmem p⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨r, s⟩, hp⟩ ⟨⟨r', s'⟩, hp'⟩ h
    simp only [Finset.mem_filter, Finset.mem_product] at hp hp'
    simp only [Subtype.mk.injEq] at h
    have hrr : r = r' := hR.2.2 r hp.1.1 r' hp'.1.1 (QuotientGroup.eq.mp h)
    subst hrr
    have h1 : ((r * s : G) : G ⧸ H) = ((r * s' : G) : G ⧸ H) := hp.2.trans hp'.2.symm
    have h2 : s⁻¹ * s' ∈ H := by
      have := QuotientGroup.eq.mp h1
      simpa [mul_assoc] using this
    have hss : s = s' := hS.2.2 s hp.1.2 s' hp'.1.2 h2
    subst hss
    rfl
  · rintro ⟨q, y, rfl, hya, hyb⟩
    obtain ⟨r, hr, hry⟩ := hR.2.1 y hya
    have hrc : r⁻¹ * c ∈ dcoset H b := by
      have : r⁻¹ * c = (r⁻¹ * y) * (y⁻¹ * c) := by group
      rw [this]
      exact mem_dcoset_mul_left H hyb hry
    obtain ⟨s, hs, hsc⟩ := hS.2.1 _ hrc
    have hpT : (r, s) ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨hr, hs⟩, ?_⟩
      apply QuotientGroup.eq.mpr
      simpa [mul_assoc] using hsc
    refine ⟨⟨(r, s), hpT⟩, ?_⟩
    apply Subtype.ext
    exact QuotientGroup.eq.mpr hry

/-- Rearrangement of double Hecke sums under symmetric structure constants. -/
theorem sum_pairs_comm {V : Type*} [AddCommMonoid V] (F : G → V)
    (hF : ∀ y h, h ∈ H → F (y * h) = F y) {R S : Finset G} {a b : G}
    (hR : IsReps H R a) (hS : IsReps H S b)
    (hcount : ∀ c, heckeCount H a b c = heckeCount H b a c) :
    ∑ r ∈ R, ∑ s ∈ S, F (r * s) = ∑ s ∈ S, ∑ r ∈ R, F (s * r) := by
  classical
  let Fb : G ⧸ H → V := Quotient.lift (s := QuotientGroup.leftRel H) F (fun x y hxy => by
    have hxy' : x⁻¹ * y ∈ H := QuotientGroup.leftRel_apply.mp hxy
    have := hF x _ hxy'
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hFb : ∀ y, F y = Fb (y : G ⧸ H) := fun y => rfl
  let g : G × G → G ⧸ H := fun p => ((p.1 * p.2 : G) : G ⧸ H)
  let Q := (R ×ˢ S).image g ∪ (S ×ˢ R).image g
  have hfib : ∀ (A B : Finset G), (∀ p ∈ A ×ˢ B, g p ∈ Q) →
      ∑ r ∈ A, ∑ s ∈ B, F (r * s) =
        ∑ q ∈ Q, ((A ×ˢ B).filter (fun p => g p = q)).card • Fb q := by
    intro A B hmaps
    rw [← Finset.sum_product' (f := fun r s => F (r * s)),
      ← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl
    intro q _
    rw [← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [hFb, ← hp.2]
  rw [hfib R S (fun p hp => Finset.mem_union_left _ (Finset.mem_image_of_mem g hp)),
    hfib S R (fun p hp => Finset.mem_union_right _ (Finset.mem_image_of_mem g hp))]
  apply Finset.sum_congr rfl
  intro q _
  induction q using QuotientGroup.induction_on with
  | H c =>
    have e1 := card_filter_eq_heckeCount H hR hS c
    have e2 := card_filter_eq_heckeCount H hS hR c
    simp only [g] at e1 e2 ⊢
    rw [e1, e2, hcount c]

/-- Symmetry of the structure constants from a multiplicative class of elements
on which Gelfand's hypothesis holds. -/
theorem heckeCount_comm_of_pred (ι : G → G) (hmul : ∀ x y, ι (x * y) = ι y * ι x)
    (hinvol : ∀ x, ι (ι x) = x) (hH : ∀ h ∈ H, ι h ∈ H) (P : G → Prop)
    (hPmul : ∀ x y, P x → P y → P (x * y)) (hPH : ∀ h ∈ H, P h)
    (hdc : ∀ x, P x → ι x ∈ dcoset H x) {a b : G} (ha : P a) (hb : P b) (c : G) :
    heckeCount H a b c = heckeCount H b a c := by
  by_cases hc : P c
  · exact heckeCount_comm H ι hmul hinvol hH a b c (hdc a ha) (hdc b hb) (hdc c hc)
  · have hPd : ∀ {a y : G}, P a → y ∈ dcoset H a → P y := by
      rintro a y ha ⟨h₁, hh₁, h₂, hh₂, rfl⟩
      exact hPmul _ _ (hPmul _ _ (hPH _ hh₁) ha) (hPH _ hh₂)
    have hempty : ∀ a b : G, P a → P b → cosetSet H a b c = ∅ := by
      intro a b ha hb
      ext q
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨y, _, hya, hyb⟩
      apply hc
      have : c = y * (y⁻¹ * c) := by group
      rw [this]
      exact hPmul _ _ (hPd ha hya) (hPd hb hyb)
    unfold heckeCount
    rw [hempty a b ha hb, hempty b a hb ha]

end TernaryPeriodPolynomials.HeckeCommutativity
