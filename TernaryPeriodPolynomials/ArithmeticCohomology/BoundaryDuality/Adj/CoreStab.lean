module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.HeckeH1

@[expose] public section


/-!
# The stabilizer of a Hecke coset and the transitions of a transversal

Let `G ⊆ 𝔾` act on the right on finitely many right cosets `G α_j` (the data `RightCosets` of a
Hecke correspondence).  The stabilizer of the coset `j₀` is the subgroup `G ∩ α_{j₀}⁻¹ G α_{j₀}`
of the elements `h` with `α_{j₀} h ∈ G α_{j₀}` (`stab`).  If `r_j ∈ G` carries the coset `j₀` to the
coset `j` (`G α_{j₀} r_j = G α_j`), then for `g ∈ G` the element `r_j g r_{j g}⁻¹` lies in the
stabilizer (`transit`); these elements satisfy the cocycle rule
`transit (g h) j = transit g j · transit h (j g)` (`transit_mul`).  They are the transitions of the
corestriction from the stabilizer to `G` with respect to the transversal `r`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjCore

open TernaryPeriodPolynomials.Spectral.HeckeH1

variable {G 𝔾 : Type} [Group G] [Group 𝔾] {embed : G →* 𝔾} (S : RightCosets embed)

/-- The identity fixes every coset. -/
theorem next_one (j : S.index) : S.next 1 j = j := by
  symm
  apply S.next_unique (h := 1)
  rw [map_one, mul_one, mul_inv_cancel]

/-- `g⁻¹` undoes the action of `g` on the cosets. -/
theorem next_inv_next (g : G) (j : S.index) : S.next g⁻¹ (S.next g j) = j := by
  rw [← S.next_mul, mul_inv_cancel, next_one]

/-- `g` undoes the action of `g⁻¹` on the cosets. -/
theorem next_next_inv (g : G) (j : S.index) : S.next g (S.next g⁻¹ j) = j := by
  have h := next_inv_next S g⁻¹ j
  rwa [inv_inv] at h

/-- **The stabilizer of the coset `j₀`**: the elements `h` with `α_{j₀} h ∈ G α_{j₀}`. -/
def stab (j₀ : S.index) : Subgroup G where
  carrier := {h | S.next h j₀ = j₀}
  mul_mem' {a b} ha hb := by
    change S.next (a * b) j₀ = j₀
    change S.next a j₀ = j₀ at ha
    change S.next b j₀ = j₀ at hb
    rw [S.next_mul, ha, hb]
  one_mem' := next_one S j₀
  inv_mem' {a} ha := by
    change S.next a⁻¹ j₀ = j₀
    change S.next a j₀ = j₀ at ha
    have h := next_inv_next S a j₀
    rwa [ha] at h

/-- Membership in the stabilizer. -/
theorem mem_stab {j₀ : S.index} {h : G} : h ∈ stab S j₀ ↔ S.next h j₀ = j₀ := Iff.rfl

variable {S} {j₀ : S.index}

/-- The transition of a stabilizer element is the conjugate by the representative. -/
theorem embed_delta_stab {h : G} (hh : h ∈ stab S j₀) :
    embed (S.delta h j₀) = S.rep j₀ * embed h * (S.rep j₀)⁻¹ := by
  rw [S.delta_spec, (mem_stab S).mp hh]

/-- The transition of a stabilizer element at `j₀` multiplies: on the stabilizer it is the
homomorphism `h ↦ α_{j₀} h α_{j₀}⁻¹`. -/
theorem delta_stab_mul (embedded : Function.Injective embed) {h k : G} (hh : h ∈ stab S j₀) :
    S.delta (h * k) j₀ = S.delta h j₀ * S.delta k j₀ := by
  rw [S.delta_mul embedded, (mem_stab S).mp hh]

variable (r : S.index → G) (hr : ∀ j, S.next (r j) j₀ = j)

include hr in
/-- The element `r_j g r_{j g}⁻¹` stabilizes the coset `j₀`. -/
theorem transit_mem (g : G) (j : S.index) : r j * g * (r (S.next g j))⁻¹ ∈ stab S j₀ := by
  have key : ∀ k, S.next (r k)⁻¹ k = j₀ := fun k => by
    have h := next_inv_next S (r k) j₀
    rwa [hr k] at h
  rw [mem_stab, S.next_mul, S.next_mul, hr, key]

/-- **The transition** `r_j g r_{j g}⁻¹` of the transversal `r`, as an element of the stabilizer. -/
def transit (g : G) (j : S.index) : stab S j₀ :=
  ⟨r j * g * (r (S.next g j))⁻¹, transit_mem r hr g j⟩

/-- The transition, as an element of `G`. -/
theorem transit_val (g : G) (j : S.index) :
    (transit r hr g j : G) = r j * g * (r (S.next g j))⁻¹ := rfl

/-- **The cocycle rule of the transitions.** -/
theorem transit_mul (g h : G) (j : S.index) :
    transit r hr (g * h) j = transit r hr g j * transit r hr h (S.next g j) := by
  apply Subtype.ext
  simp only [transit_val, Subgroup.coe_mul, S.next_mul]
  group

/-- The transition of the identity is trivial. -/
theorem transit_one (j : S.index) : transit r hr 1 j = 1 := by
  apply Subtype.ext
  simp only [transit_val, next_one, mul_one, mul_inv_cancel, Subgroup.coe_one]

/-- `r_j g = transit g j · r_{j g}`. -/
theorem transit_mul_rep (g : G) (j : S.index) :
    (transit r hr g j : G) * r (S.next g j) = r j * g := by
  rw [transit_val, inv_mul_cancel_right]

end TernaryPeriodPolynomials.BoundaryDuality.AdjCore
