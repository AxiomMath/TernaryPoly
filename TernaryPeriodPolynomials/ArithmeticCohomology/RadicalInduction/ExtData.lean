module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.Lattice
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.RadicalAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalLevi

@[expose] public section


/-!
# A split sub-extension of finite index with radical `mℤ²`

Formalized by Claude Sonnet 5.5.

`Compat ext s Stab ext' s' ιL m0`: `Stab ≤ S` is the split extension `ext'` of `L' ↪ L` whose radical is `m₀ ℤ² ⊆ ℤ²` and whose splitting is the restriction of `s`, and the Levi elements
of `ext` act on the radical with determinant one.  Consequences: every element of `S` is `inl n · s ℓ` (`exists_decomp`); the radical elements `inl (r ^ m₀)` are normal (`conj_pow_mem`);
`inl n ∈ Stab` iff `n ∈ latt m₀` (`inl_mem_iff`); `rightHom (Stab) ⊆ range ιL` (`rightHom_mem_range`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD

variable {S L E₂ L' : Type} [Group S] [Group L] [Group E₂] [Group L'] (ext : GroupExtension RadicalLattice S L) (s : ext.Splitting)
  (Stab : Subgroup S) (α : E₂ →* S) (ext' : GroupExtension RadicalLattice E₂ L') (s' : ext'.Splitting) (ιL : L' →* L) (m0 : ℕ)

/-- The compatibility of the split extension `ext'` (mapped into `S` by `α`, with image `Stab`) with `S`. -/
structure Compat : Prop where
  range_eq : α.range = Stab
  inl_eq : ∀ r, α (ext'.inl r) = ext.inl (r ^ m0)
  split_eq : ∀ m, α (s' m) = s (ιL m)
  inj : Function.Injective ιL
  det : ∀ ℓ : L, radDet (splitRadicalInput s ℓ) = 1

variable {ext s Stab α ext' s' ιL m0}

theorem Compat.mem_stab (hc : Compat ext s Stab α ext' s' ιL m0) (g : E₂) : α g ∈ Stab := by
  rw [← hc.range_eq]
  exact ⟨g, rfl⟩

theorem exists_decomp (e : S) : ∃ n : RadicalLattice, e = ext.inl n * s (ext.rightHom e) := by
  have h : e * (s (ext.rightHom e))⁻¹ ∈ ext.rightHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, GroupExtension.Splitting.rightHom_splitting, mul_inv_cancel]
  rw [← ext.range_inl_eq_ker_rightHom] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [hn, inv_mul_cancel_right]⟩

theorem conj_inl (ℓ : L) (r : RadicalLattice) : (s ℓ)⁻¹ * ext.inl r * s ℓ = ext.inl (splitRadicalInput s ℓ r) := by
  have h := splitRadicalInput_commute s ℓ r
  rw [mul_assoc, h, inv_mul_cancel_left]

variable (hc : Compat ext s Stab α ext' s' ιL m0)

include hc in
theorem conj_pow_mem (e : S) (r : RadicalLattice) : e⁻¹ * ext.inl (r ^ m0) * e ∈ Stab := by
  obtain ⟨n, hn⟩ := exists_decomp (ext := ext) (s := s) e
  set ℓ := ext.rightHom e with hℓ
  have h1 : (ext.inl n)⁻¹ * ext.inl (r ^ m0) * ext.inl n = ext.inl (r ^ m0) := by
    rw [← map_inv, ← map_mul, ← map_mul, mul_comm n⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have key : e⁻¹ * ext.inl (r ^ m0) * e = α (ext'.inl (splitRadicalInput s ℓ r)) := by
    calc e⁻¹ * ext.inl (r ^ m0) * e = (s ℓ)⁻¹ * ((ext.inl n)⁻¹ * ext.inl (r ^ m0) * ext.inl n) * s ℓ := by
          rw [hn]; group
      _ = ext.inl (splitRadicalInput s ℓ (r ^ m0)) := by rw [h1, conj_inl]
      _ = α (ext'.inl (splitRadicalInput s ℓ r)) := by rw [hc.inl_eq, map_pow]
  rw [key, ← hc.range_eq]
  exact ⟨_, rfl⟩

include hc in
theorem stab_decomp (x : E₂) : ∃ (r : RadicalLattice) (m : L'),
    α x = ext.inl (r ^ m0) * s (ιL m) := by
  obtain ⟨r, hr⟩ := exists_decomp (ext := ext') (s := s') x
  refine ⟨r, ext'.rightHom x, ?_⟩
  have := congrArg α hr
  simpa [hc.inl_eq, hc.split_eq] using this

include hc in
theorem rightHom_stab (x : S) (hx : x ∈ Stab) : ext.rightHom x ∈ ιL.range := by
  rw [← hc.range_eq] at hx
  obtain ⟨x₂, rfl⟩ := hx
  obtain ⟨r, m, h⟩ := stab_decomp hc x₂
  rw [h, map_mul, GroupExtension.rightHom_inl, GroupExtension.Splitting.rightHom_splitting, one_mul]
  exact ⟨m, rfl⟩

include hc in
theorem inl_mem_iff (n : RadicalLattice) : ext.inl n ∈ Stab ↔ n ∈ latt m0 := by
  constructor
  · intro hn
    rw [← hc.range_eq] at hn
    obtain ⟨x₂, hx₂⟩ := hn
    obtain ⟨r, m, h'⟩ := stab_decomp hc x₂
    have h : ext.inl n = ext.inl (r ^ m0) * s (ιL m) := hx₂.symm.trans h'
    have h1 : ext.rightHom (ext.inl n) = 1 := GroupExtension.rightHom_inl _ _
    have h2 : ext.rightHom (ext.inl (r ^ m0) * s (ιL m)) = ιL m := by
      rw [map_mul, GroupExtension.rightHom_inl, GroupExtension.Splitting.rightHom_splitting, one_mul]
    have h3 : ext.rightHom (ext.inl n) = ext.rightHom (ext.inl (r ^ m0) * s (ιL m)) := by
      simpa using congrArg ext.rightHom h
    rw [h1, h2] at h3
    have hm : m = 1 := hc.inj (by rw [map_one]; exact h3.symm)
    subst hm
    simp only [map_one, mul_one] at h
    exact ⟨r, (ext.inl_injective h).symm⟩
  · rintro ⟨r, rfl⟩
    have e : ext.inl ((powMonoidHom m0 : RadicalLattice →* RadicalLattice) r) = α (ext'.inl r) := (hc.inl_eq r).symm
    rw [e, ← hc.range_eq]
    exact ⟨_, rfl⟩

end TernaryPeriodPolynomials.Argument.RadicalInduction
