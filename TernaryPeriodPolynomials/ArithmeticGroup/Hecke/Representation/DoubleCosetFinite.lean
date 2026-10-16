module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.FixedHecke

@[expose] public section


/-!
# Finite double cosets from finite-index intersections

If `K ∩ γ K γ⁻¹` has finite index in `K`, the double coset `K γ K` is a finite union of left
cosets, with explicit representatives `q γ` for `q` running over `K / (K ∩ γ K γ⁻¹)`.
Double coset data transport along injective homomorphisms.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

namespace TernaryPeriodPolynomials.RepresentationTheory

variable {G : Type*} [Group G]

/-- `K ∩ γ K γ⁻¹`, as a subgroup of `K`. -/
def conjIntersection (K : Subgroup G) (γ : G) : Subgroup K :=
  (K.map (MulAut.conj γ).toMonoidHom).subgroupOf K

theorem mem_conjIntersection {K : Subgroup G} {γ : G} {k : K} :
    k ∈ conjIntersection K γ ↔ γ⁻¹ * k.val * γ ∈ K := by
  unfold conjIntersection
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxk⟩
    have : (k : G) = γ * x * γ⁻¹ := by rw [← hxk]; rfl
    rw [this]; simpa [mul_assoc] using hx
  · intro h
    refine ⟨γ⁻¹ * k.val * γ, h, ?_⟩
    change γ * (γ⁻¹ * k.val * γ) * γ⁻¹ = k.val
    group

/-- Double coset representatives from a finite quotient `K / (K ∩ γ K γ⁻¹)`. -/
def DoubleCoset.ofFinite (K : Subgroup G) (γ : G) [Finite (K ⧸ conjIntersection K γ)] :
    DoubleCoset K := by
  classical
  let _ : Fintype (K ⧸ conjIntersection K γ) := Fintype.ofFinite _
  exact
  { g := γ
    reps := Finset.univ.image (fun c : K ⧸ conjIntersection K γ => (Quotient.out c : K).val * γ)
    inDouble := by
      intro r hr
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
      exact ⟨Quotient.out c, 1, by simp⟩
    complete := by
      intro a b
      refine ⟨(Quotient.out (QuotientGroup.mk a : K ⧸ conjIntersection K γ) : K).val * γ,
        Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
      set q : K := Quotient.out (QuotientGroup.mk a : K ⧸ conjIntersection K γ)
      have hq : (QuotientGroup.mk q : K ⧸ conjIntersection K γ) = QuotientGroup.mk a :=
        QuotientGroup.out_eq' _
      have hmem : q⁻¹ * a ∈ conjIntersection K γ := QuotientGroup.eq.mp hq
      have h2 := mem_conjIntersection.mp hmem
      have : (q.val * γ)⁻¹ * (a.val * γ * b.val) = (γ⁻¹ * (q⁻¹ * a).val * γ) * b.val := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [this]
      exact K.mul_mem h2 b.property
    disjoint := by
      intro r hr t ht hrt
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp ht
      have hK : (Quotient.out c : K)⁻¹ * Quotient.out d ∈ conjIntersection K γ := by
        apply mem_conjIntersection.mpr
        have : γ⁻¹ * ((Quotient.out c : K)⁻¹ * Quotient.out d).val * γ =
            ((Quotient.out c : K).val * γ)⁻¹ * ((Quotient.out d : K).val * γ) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        rw [this]; exact hrt
      have hcd : c = d := by
        rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]
        exact QuotientGroup.eq.mpr hK
      rw [hcd] }

@[simp] theorem DoubleCoset.ofFinite_g (K : Subgroup G) (γ : G) [Finite (K ⧸ conjIntersection K γ)] :
    (DoubleCoset.ofFinite K γ).g = γ := rfl

/-- Transport of double coset data along an injective homomorphism. -/
def DoubleCoset.map {G' : Type*} [Group G'] {K : Subgroup G} (φ : G →* G')
    (hφ : Function.Injective φ) (T : DoubleCoset K) : DoubleCoset (K.map φ) := by
  classical
  exact
  { g := φ T.g
    reps := T.reps.image φ
    inDouble := by
      intro r hr
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨a, b, rfl⟩ := T.inDouble s hs
      exact ⟨⟨φ a, Subgroup.mem_map_of_mem φ a.property⟩, ⟨φ b, Subgroup.mem_map_of_mem φ b.property⟩,
        by simp [map_mul]⟩
    complete := by
      rintro ⟨_, ⟨a, ha, rfl⟩⟩ ⟨_, ⟨b, hb, rfl⟩⟩
      obtain ⟨r, hr, hmem⟩ := T.complete ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨φ r, Finset.mem_image_of_mem φ hr, ?_⟩
      have := Subgroup.mem_map_of_mem φ hmem
      simpa [map_mul, map_inv] using this
    disjoint := by
      intro r hr t ht hrt
      obtain ⟨r', hr', rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hrt
      have : x = r'⁻¹ * t' := hφ (by rw [hxe, map_mul, map_inv])
      rw [T.disjoint r' hr' t' ht' (this ▸ hx)] }

@[simp] theorem DoubleCoset.map_g {G' : Type*} [Group G'] {K : Subgroup G} (φ : G →* G')
    (hφ : Function.Injective φ) (T : DoubleCoset K) : (T.map φ hφ).g = φ T.g := rfl

end TernaryPeriodPolynomials.RepresentationTheory
