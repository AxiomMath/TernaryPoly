module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.ExtData
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.FunAlt

@[expose] public section


/-!
# The radical orbits on `S / Stab`

Formalized by Claude Sonnet 5.5.

The radical lattice acts on `Y = S ⧸ Stab` through `inl`.  The map `S/Stab → L/L'` has the radical orbits as fibres; each orbit has `m₀²` elements, so for a radical-invariant `H` on `Y`,
`∑_{y ∈ Y} H(y) = m₀² ∑_{x ∈ L/L'} H(s(x) · y₀)` (`sum_orbits`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD

variable {S L L' : Type} [Group S] [Group L] [Group L'] {ext : GroupExtension RadicalLattice S L} {s : ext.Splitting}
  {Stab : Subgroup S} {E₂ : Type} [Group E₂] {α : E₂ →* S} {ext' : GroupExtension RadicalLattice E₂ L'} {s' : ext'.Splitting} {ιL : L' →* L} {m0 : ℕ}
  {Lsub : Subgroup L}

/-- `S ⧸ Stab` with the action of the radical lattice through `inl`. -/
def YN (_ext : GroupExtension RadicalLattice S L) (Stab : Subgroup S) : Type := S ⧸ Stab

instance (ext : GroupExtension RadicalLattice S L) (Stab : Subgroup S) : MulAction RadicalLattice (YN ext Stab) :=
  MulAction.compHom (S ⧸ Stab) ext.inl

/-- The point of `YN` of an element of `S`. -/
def YN.mk (ext : GroupExtension RadicalLattice S L) (Stab : Subgroup S) (e : S) : YN ext Stab := QuotientGroup.mk e

theorem YN_smul (n : RadicalLattice) (e : S) : n • YN.mk ext Stab e = YN.mk ext Stab (ext.inl n * e) := rfl

/-- The projection to the Levi cosets. -/
def piY (hc : Compat ext s Stab α ext' s' ιL m0) (hr : ιL.range = Lsub) : YN ext Stab → L ⧸ Lsub :=
  Quotient.map' (s₁ := QuotientGroup.leftRel Stab) (s₂ := QuotientGroup.leftRel Lsub) ext.rightHom (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [← map_inv, ← map_mul, ← hr]
    exact rightHom_stab hc _ hab)

theorem piY_mk (hc : Compat ext s Stab α ext' s' ιL m0) (hr : ιL.range = Lsub) (e : S) :
    piY hc hr (YN.mk ext Stab e) = QuotientGroup.mk (ext.rightHom e) := rfl

/-- The base point of the orbit over the Levi coset `x`. -/
def yBase (ext : GroupExtension RadicalLattice S L) (s : ext.Splitting) (Stab : Subgroup S) (x : L ⧸ Lsub) :
    YN ext Stab := YN.mk ext Stab (s (Quotient.out x))

theorem fiber_eq_orbit (hc : Compat ext s Stab α ext' s' ιL m0) (hr : ιL.range = Lsub) (x : L ⧸ Lsub) (y : YN ext Stab) :
    piY hc hr y = x ↔ y ∈ MulAction.orbit RadicalLattice (yBase ext s Stab x) := by
  subst hr
  constructor
  · intro h
    induction y using QuotientGroup.induction_on with
    | H e =>
      change piY hc rfl (YN.mk ext Stab e) = x at h
      rw [piY_mk] at h
      obtain ⟨n, hn⟩ := exists_decomp (ext := ext) (s := s) e
      have hx : (QuotientGroup.mk (Quotient.out x) : L ⧸ ιL.range) = x := Quotient.out_eq' x
      have h2 : (QuotientGroup.mk (ext.rightHom e) : L ⧸ ιL.range) = QuotientGroup.mk (Quotient.out x) := by
        rw [h, hx]
      have hmem : (Quotient.out x)⁻¹ * ext.rightHom e ∈ ιL.range := QuotientGroup.eq.mp h2.symm
      obtain ⟨m, hm⟩ := hmem
      have hr : ext.rightHom e = Quotient.out x * ιL m := by
        rw [hm]; group
      refine ⟨n, ?_⟩
      show YN.mk ext Stab (ext.inl n * s (Quotient.out x)) = YN.mk ext Stab e
      show (QuotientGroup.mk (ext.inl n * s (Quotient.out x)) : S ⧸ Stab) = QuotientGroup.mk e
      rw [QuotientGroup.eq]
      have he : e = ext.inl n * (s (Quotient.out x) * s (ιL m)) := by
        conv_lhs => rw [hn]
        rw [hr, map_mul]
      have : (ext.inl n * s (Quotient.out x))⁻¹ * e = s (ιL m) := by
        rw [he]; group
      rw [this, ← hc.split_eq m]
      rw [← hc.range_eq]
      exact ⟨s' m, rfl⟩
  · rintro ⟨n, rfl⟩
    show piY hc rfl (YN.mk ext Stab (ext.inl n * s (Quotient.out x))) = x
    rw [piY_mk, map_mul, GroupExtension.rightHom_inl, GroupExtension.Splitting.rightHom_splitting, one_mul]
    exact Quotient.out_eq' x

theorem splitRadicalInput_surjective (ℓ : L) : Function.Surjective (splitRadicalInput s ℓ) := by
  intro r
  refine ⟨splitRadicalInput s ℓ⁻¹ r, ?_⟩
  rw [← splitRadicalInput_mul, inv_mul_cancel, splitRadicalInput_one]

theorem stabilizer_yBase (hc : Compat ext s Stab α ext' s' ιL m0) (x : L ⧸ Lsub) :
    MulAction.stabilizer RadicalLattice (yBase ext s Stab x) = (latt m0).comap (splitRadicalInput s (Quotient.out x)) := by
  ext n
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap]
  show YN.mk ext Stab (ext.inl n * s (Quotient.out x)) = YN.mk ext Stab (s (Quotient.out x)) ↔ _
  show (QuotientGroup.mk (ext.inl n * s (Quotient.out x)) : S ⧸ Stab) = QuotientGroup.mk (s (Quotient.out x)) ↔ _
  rw [QuotientGroup.eq, ← inl_mem_iff hc, ← conj_inl, ← Subgroup.inv_mem_iff]
  have : ((ext.inl n * s (Quotient.out x))⁻¹ * s (Quotient.out x))⁻¹ = (s (Quotient.out x))⁻¹ * ext.inl n * s (Quotient.out x) := by
    group
  rw [this]

theorem card_fiber (hc : Compat ext s Stab α ext' s' ιL m0) (hr : ιL.range = Lsub) [NeZero m0] [Fintype (YN ext Stab)]
    [DecidableEq (L ⧸ Lsub)] (x : L ⧸ Lsub) : (Finset.univ.filter (fun y : YN ext Stab => piY hc hr y = x)).card = m0 ^ 2 := by
  have h1 : ((Finset.univ.filter (fun y : YN ext Stab => piY hc hr y = x) : Finset (YN ext Stab)) : Set (YN ext Stab)) =
      MulAction.orbit RadicalLattice (yBase ext s Stab x) := by
    ext y
    simp [fiber_eq_orbit hc hr]
  have h2 := MulAction.index_stabilizer RadicalLattice (yBase ext s Stab x)
  rw [stabilizer_yBase hc, Subgroup.index_comap_of_surjective _ (splitRadicalInput_surjective _), index_latt] at h2
  rw [← h1, Set.ncard_coe_finset] at h2
  exact h2.symm

theorem sum_orbits (hc : Compat ext s Stab α ext' s' ιL m0) (hr : ιL.range = Lsub) [NeZero m0] [Fintype (YN ext Stab)] [Fintype (L ⧸ Lsub)]
    (H : YN ext Stab → ℂ) (hH : ∀ (n : RadicalLattice) (y : YN ext Stab), H (n • y) = H y) :
    ∑ y, H y = ((m0 ^ 2 : ℕ) : ℂ) * ∑ x : L ⧸ Lsub, H (yBase ext s Stab x) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := piY hc hr) (fun _ _ => Finset.mem_univ _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have h : ∀ y ∈ Finset.univ.filter (fun y : YN ext Stab => piY hc hr y = x), H y = H (yBase ext s Stab x) := by
    intro y hy
    have := (fiber_eq_orbit hc hr x y).mp (Finset.mem_filter.mp hy).2
    obtain ⟨n, rfl⟩ := this
    exact hH n _
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_fiber hc hr x, nsmul_eq_mul]

end TernaryPeriodPolynomials.Argument.RadicalInduction
