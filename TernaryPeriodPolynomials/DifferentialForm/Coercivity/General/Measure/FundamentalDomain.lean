module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Measure.SpaceVolume
public import Mathlib.MeasureTheory.Group.FundamentalDomain

@[expose] public section


/-!
# General coercivity: a measurable fundamental domain for an admissible group

Mathlib has no existence theorem for fundamental domains, so one is constructed here.  Cover `Space`
by a countable family of open sets `Wᵢ` whose nontrivial `Γ`-translates are disjoint from themselves
(available because the action is free with finite compact transporters), and take
`t = ⋃ᵢ (Wᵢ \ ⋃_{j<i} Γ·Wⱼ)`.  Every orbit meets `t` in exactly one point.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MeasureTheory Set TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering

variable {Γ : Subgroup RealGL}

/-- Every orbit of an admissible group meets a suitable measurable set in exactly one point. -/
theorem Admissible.exists_unique_section (h : Admissible Γ) :
    ∃ t : Set Space, MeasurableSet t ∧ ∀ x : Space, ∃! g : Γ, g • x ∈ t := by
  classical
  have : Countable Γ := h.countable
  have : Nonempty Space := ⟨⟨_, traceOnePositive_nonempty.choose_spec⟩⟩
  have hex : ∀ S : Space, ∃ U : Set Space, IsOpen U ∧ S ∈ U ∧
      ∀ g : Γ, g ≠ 1 → Disjoint ((g • ·) '' U) U :=
    fun S => exists_open_disjoint_translates h.transporters h.free' S
  choose U hUo hUS hUd using hex
  obtain ⟨f, hf⟩ := isLindelof_univ.indexed_countable_subcover U hUo
    (fun S _ => Set.mem_iUnion.mpr ⟨S, hUS S⟩)
  let W : ℕ → Set Space := fun i => U (f i)
  let R : ℕ → Set Space := fun i => ⋃ j ∈ Set.Iio i, ⋃ γ : Γ, (γ • ·) '' W j
  have hWo : ∀ i, IsOpen (W i) := fun i => hUo _
  have hRo : ∀ i, IsOpen (R i) := by
    intro i
    refine isOpen_biUnion fun j _ => isOpen_iUnion fun γ => ?_
    exact (actionHomeomorph (γ : RealGL)).isOpenMap _ (hWo j)
  have hcover : ∀ x : Space, ∃ i, ∃ γ : Γ, γ • x ∈ W i := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hf (Set.mem_univ x))
    exact ⟨i, 1, by simpa using hi⟩
  have hnot : ∀ (x : Space) (i : ℕ) (γ : Γ), γ • x ∈ R i → ∃ j < i, ∃ γ' : Γ, γ' • x ∈ W j := by
    intro x i γ hγ
    obtain ⟨j, hj, hγ'⟩ := Set.mem_iUnion₂.mp hγ
    obtain ⟨γ'', y, hy, hyx⟩ := Set.mem_iUnion.mp hγ'
    refine ⟨j, hj, γ''⁻¹ * γ, ?_⟩
    have : (γ''⁻¹ * γ) • x = y := by
      rw [mul_smul, ← hyx]
      exact inv_smul_smul γ'' y
    rw [this]
    exact hy
  let t : Set Space := ⋃ i, (W i \ R i)
  refine ⟨t, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun i => (hWo i).measurableSet.diff (hRo i).measurableSet
  · intro x
    have hmin : ∀ (γ : Γ) (i : ℕ), γ • x ∈ W i \ R i → ∀ j < i, ∀ γ' : Γ, γ' • x ∉ W j := by
      intro γ i hγ j hj γ' hγ'
      apply hγ.2
      exact Set.mem_iUnion₂.mpr ⟨j, hj, Set.mem_iUnion.mpr ⟨γ * γ'⁻¹, γ' • x, hγ', by
        show (γ * γ'⁻¹) • γ' • x = γ • x
        rw [smul_smul, inv_mul_cancel_right]⟩⟩
    have hex : ∃ γ : Γ, γ • x ∈ t := by
      have hc := hcover x
      obtain ⟨γ0, hγ0⟩ := Nat.find_spec hc
      refine ⟨γ0, Set.mem_iUnion.mpr ⟨Nat.find hc, hγ0, fun hR => ?_⟩⟩
      obtain ⟨j, hj, γ', hγ'⟩ := hnot x _ γ0 hR
      exact Nat.find_min hc hj ⟨γ', hγ'⟩
    refine existsUnique_of_exists_of_unique hex ?_
    intro γ₁ γ₂ h1 h2
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h2
    have hij : i = j := by
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exact (hmin γ₂ j hj i hlt γ₁ hi.1).elim
      · exact heq
      · exact (hmin γ₁ i hi j hgt γ₂ hj.1).elim
    subst hij
    by_contra hne
    have hne' : γ₂ * γ₁⁻¹ ≠ 1 := fun h' => hne (mul_inv_eq_one.mp h').symm
    exact Set.disjoint_left.mp (hUd (f i) _ hne')
      ⟨γ₁ • x, hi.1, by
        show (γ₂ * γ₁⁻¹) • γ₁ • x = γ₂ • x
        rw [smul_smul, inv_mul_cancel_right]⟩ hj.1

/-- An admissible group has a measurable fundamental domain for the Riemannian volume. -/
theorem Admissible.exists_isFundamentalDomain (h : Admissible Γ) :
    ∃ t : Set Space, MeasurableSet t ∧ MeasureTheory.IsFundamentalDomain Γ t spaceVolume := by
  obtain ⟨t, ht, hu⟩ := h.exists_unique_section
  exact ⟨t, ht, MeasureTheory.IsFundamentalDomain.mk' ht.nullMeasurableSet hu⟩

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
