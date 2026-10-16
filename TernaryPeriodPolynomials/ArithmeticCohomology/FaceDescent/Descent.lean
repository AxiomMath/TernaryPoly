module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.Isotypic

@[expose] public section


/-!
# The descended face pairing is perfect

Formalized by Claude Sonnet 5.5.

Let `G` be the finite covering group of a face (the face stabilizer of the big group modulo the principal congruence subgroup), acting on the mixed cuspidal groups `𝒞_R(E)`, `𝒞_R(E*)` with **all determinant and reflection actions retained**.
The face pairing is the composite of the Koszul pairing on the radical and the Poincaré-Lefschetz pairing of the modular curve; `g` scales the first by the determinant character `δ(g)` of its action on the radical lattice
(`radDet_rowAct`, `PhiC_pullback`) and the second by the orientation character `δ(g)` of the modular curve (`cuspConjNat`).  Then
the pairing satisfies `⟨g x, g y⟩ = δ(g)² ⟨x, y⟩ = ⟨x, y⟩`, and `face_pairing_descends` says that the restriction to the `G`-invariants is still perfect (and the two spaces of invariants have the same dimension).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

variable {G V W : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

omit [Fintype G] in
/-- The pairing, as the product of the two internal orientation characters `δ_N`, `δ_L` (the Koszul and the Poincaré-Lefschetz scalings), is `δ_N δ_L`-equivariant. -/
theorem face_pairing_equivariant (e : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (δN δL : G →* ℤˣ) (hδ : ∀ g, δN g * δL g = 1)
    (hscale : ∀ g x y, e (ρ g x) (σ g y) = (δN g : ℂ) * (δL g : ℂ) * e x y) (g : G) (x : V) (y : W) :
    e (ρ g x) (σ g y) = e x y := by
  have h : (δN g : ℂ) * (δL g : ℂ) = 1 := by
    have := congrArg (fun z : ℤˣ => ((z : ℤ) : ℂ)) (hδ g)
    simpa using this
  rw [hscale, h, one_mul]

/-- **The descended pairing is perfect** (left): the restriction of a perfect face pairing to the invariants of the finite covering group, with the orientation characters retained, has trivial left kernel. -/
theorem face_pairing_descends_left (e : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (δN δL : G →* ℤˣ) (hδ : ∀ g, δN g * δL g = 1)
    (hscale : ∀ g x y, e (ρ g x) (σ g y) = (δN g : ℂ) * (δL g : ℂ) * e x y) (hL : ∀ v, (∀ w, e v w = 0) → v = 0)
    (v : isoSub ρ 1) (h : ∀ w, isoPairing (ρ := ρ) (σ := σ) e 1 1 v w = 0) : v = 0 :=
  isoPairing_left e 1 1 1 (fun g => by simp) (fun g x y => by simpa using face_pairing_equivariant e δN δL hδ hscale g x y) hL v h

/-- Right kernel. -/
theorem face_pairing_descends_right (e : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (δN δL : G →* ℤˣ) (hδ : ∀ g, δN g * δL g = 1)
    (hscale : ∀ g x y, e (ρ g x) (σ g y) = (δN g : ℂ) * (δL g : ℂ) * e x y) (hR : ∀ w, (∀ v, e v w = 0) → w = 0)
    (w : isoSub σ 1) (h : ∀ v, isoPairing (ρ := ρ) (σ := σ) e 1 1 v w = 0) : w = 0 :=
  isoPairing_right e 1 1 1 (fun g => by simp) (fun g x y => by simpa using face_pairing_equivariant e δN δL hδ hscale g x y) hR w h

/-- **The invariants have the same dimension** (finite-dimensional case). -/
theorem face_pairing_descends_finrank [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (e : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (δN δL : G →* ℤˣ) (hδ : ∀ g, δN g * δL g = 1)
    (hscale : ∀ g x y, e (ρ g x) (σ g y) = (δN g : ℂ) * (δL g : ℂ) * e x y) (hL : ∀ v, (∀ w, e v w = 0) → v = 0)
    (hR : ∀ w, (∀ v, e v w = 0) → w = 0) :
    Module.finrank ℂ (isoSub ρ 1) = Module.finrank ℂ (isoSub σ 1) :=
  isoPairing_finrank_eq e 1 1 1 (fun g => by simp) (fun g x y => by simpa using face_pairing_equivariant e δN δL hδ hscale g x y) hL hR

omit [Fintype G] in
/-- **If the two characters do not cancel, the pairing kills the invariants**: this is why the characters must multiply to the (trivial) face orientation. -/
theorem face_pairing_zero_on_invariants (e : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (δN δL : G →* ℤˣ)
    (hscale : ∀ g x y, e (ρ g x) (σ g y) = (δN g : ℂ) * (δL g : ℂ) * e x y) (g₀ : G) (hg₀ : δN g₀ * δL g₀ ≠ 1)
    {v : V} (hv : v ∈ isoSub ρ 1) {w : W} (hw : w ∈ isoSub σ 1) : e v w = 0 := by
  have h := hscale g₀ v w
  rw [hv g₀, hw g₀] at h
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h
  have hne : ((δN g₀ : ℤ) : ℂ) * ((δL g₀ : ℤ) : ℂ) ≠ 1 := by
    intro h1
    apply hg₀
    have h2 : (((δN g₀ * δL g₀ : ℤˣ) : ℤ) : ℂ) = 1 := by simpa using h1
    have h3 : ((δN g₀ * δL g₀ : ℤˣ) : ℤ) = 1 := by exact_mod_cast h2
    exact Units.ext (by simpa using h3)
  have : (((δN g₀ : ℤ) : ℂ) * ((δL g₀ : ℤ) : ℂ) - 1) * e v w = 0 := by linear_combination -h
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd (sub_eq_zero.1 h0) hne
  · exact h0

end TernaryPeriodPolynomials.Argument.FaceDescent
