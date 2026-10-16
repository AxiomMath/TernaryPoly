module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.TubeProper

@[expose] public section


/-!
# Lemma 3.3, G3: the geometric frame around the identity form

For a closed `Γ(6)`-invariant set `R` of the symmetric space meeting the flat only in the identity form
(the supports of the cell cycles) and a closed set `R₂` missing the flat (the lower cells), `frame`
produces the coordinate box `T̃ = {‖π‖ < ε, ‖t‖ < R0}` around the identity, the slab level `δ`, a thin tube
radius `ρ'` (with the properness of `tube_proper`) and a `Γ(6)`-invariant open neighbourhood `D` of `R`
such that

* the translates of the closed box are pairwise disjoint (the box is a chart of the quotient) and the
  nontrivial ones miss the tube;
* `D` meets the box only in the slab `{‖t‖ < δ}` and meets the tube only inside the box;
* the lower cells stay outside the tube.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceArithmeticProper
  TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

/-- The tube `{‖π‖ ≤ ρ'}`. -/
def tube (ρ' : Space → ℝ) : Set Space := {S | ‖piR3 S‖ ≤ ρ' S}

theorem isClosed_tube {ρ' : Space → ℝ} (hρ : Continuous ρ') : IsClosed (tube ρ') :=
  isClosed_le (continuous_norm.comp piR3.continuous) hρ

/-- Only finitely many translates of the tube meet a compact set (inverse form of `tube_proper`). -/
theorem tube_finite_inv {ρ' : Space → ℝ}
    (hfin : ∀ K : Set Space, IsCompact K → {g : principalSix | ((g • K) ∩ tube ρ').Nonempty}.Finite)
    (L : Set Space) (hL : IsCompact L) :
    {g : principalSix | ((g • tube ρ') ∩ L).Nonempty}.Finite := by
  refine ((hfin L hL).preimage (inv_injective.injOn)).subset ?_
  rintro g ⟨y, hy, hyL⟩
  obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hy
  refine ⟨z, ?_, hz⟩
  exact Set.mem_smul_set.mpr ⟨g • z, hyL, by simp⟩

/-- The union of all translates is invariant. -/
theorem smul_mem_saturation_iff (g : principalSix) (A : Set Space) (x : Space) :
    g • x ∈ (⋃ h : principalSix, h • A) ↔ x ∈ (⋃ h : principalSix, h • A) := by
  simp only [Set.mem_iUnion, Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨g⁻¹ * h, ?_⟩
    simpa [mul_smul, mul_inv_rev, inv_inv] using hh
  · rintro ⟨h, hh⟩
    refine ⟨g * h, ?_⟩
    simpa [mul_smul, mul_inv_rev] using hh

/-- Away from the identity form, the retract is bounded away from the flat in the shell. -/
theorem exists_shell_free (R : Set Space) (hRc : IsClosed R) (hRF : ∀ S ∈ R, S ∈ flat → S = p0)
    (δ R0 : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ S ∈ R, ‖piR3 S‖ ≤ ε → δ ≤ ‖(coordHomeo S).2‖ →
      ‖(coordHomeo S).2‖ ≤ R0 → False := by
  by_contra hcon
  push Not at hcon
  let K0 : Set Space := (R ∩ boxC 1 R0) ∩ {S | δ ≤ ‖(coordHomeo S).2‖}
  have hK0 : IsCompact K0 := by
    refine ((isCompact_boxC 1 R0).inter_left hRc).inter_right ?_
    exact isClosed_le continuous_const (continuous_norm.comp (continuous_snd.comp coordHomeo.continuous))
  let t : ℕ → Set Space := fun n => {S | ‖piR3 S‖ ≤ 1 / ((n : ℝ) + 1)}
  have htc : ∀ n, IsClosed (t n) := fun n =>
    isClosed_le (continuous_norm.comp piR3.continuous) continuous_const
  have hst : ∀ u : Finset ℕ, (K0 ∩ ⋂ i ∈ u, t i).Nonempty := by
    intro u
    obtain ⟨S, hSR, hSπ, hSδ, hSR0⟩ := hcon (1 / ((u.sup id : ℕ) + 1 : ℝ)) (by positivity)
    have hle1 : (1 : ℝ) / (((u.sup id : ℕ) : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ ((u.sup id : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    refine ⟨S, ⟨⟨hSR, ?_, ?_⟩, hSδ⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact hSπ.trans hle1
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hSR0.1
    · simp only [Set.mem_iInter]
      intro i hi
      refine hSπ.trans ?_
      have hi' : i ≤ u.sup id := Finset.le_sup (f := id) hi
      have : ((i : ℕ) : ℝ) ≤ ((u.sup id : ℕ) : ℝ) := by exact_mod_cast hi'
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
  obtain ⟨S, ⟨⟨hSR, _, _⟩, hSδ⟩, hSt⟩ := hK0.inter_iInter_nonempty t htc hst
  have hπ : ‖piR3 S‖ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    have := Set.mem_iInter.mp hSt n
    exact absurd this (not_le.mpr hn)
  have hflat : S ∈ flat := by
    have : piR3 S = 0 := norm_le_zero_iff.mp hπ
    exact this
  have hp0 := hRF S hSR hflat
  have hSδ' : δ ≤ ‖(coordHomeo S).2‖ := hSδ
  rw [hp0, coordHomeo_p0] at hSδ'
  simp at hSδ'
  linarith

/-- **The frame.**  See the module documentation. -/
theorem frame (R R₂ : Set Space) (hRc : IsClosed R)
    (hRG : ∀ (g : principalSix) (S : Space), S ∈ R → g • S ∈ R)
    (hRF : ∀ S ∈ R, S ∈ flat → S = p0) (hR₂c : IsClosed R₂) (hR₂F : ∀ S ∈ R₂, S ∉ flat) :
    ∃ (ε R0 δ : ℝ) (ρ' : Space → ℝ) (D : Set Space), 0 < ε ∧ 0 < δ ∧ δ < R0 ∧
      Continuous ρ' ∧ (∀ S, 0 < ρ' S) ∧ (∀ S, ρ' S < ε) ∧
      (∀ g : principalSix, g ≠ 1 → Disjoint (g • boxC ε R0) (boxC ε R0)) ∧
      (∀ g : principalSix, g ≠ 1 → Disjoint (g • boxC ε R0) (tube ρ')) ∧
      (∀ K : Set Space, IsCompact K → {g : principalSix | ((g • K) ∩ tube ρ').Nonempty}.Finite) ∧
      IsOpen D ∧ (∀ (g : principalSix) (S : Space), S ∈ D → g • S ∈ D) ∧ R ⊆ D ∧
      (∀ S ∈ D, S ∈ boxO ε R0 → ‖(coordHomeo S).2‖ < δ) ∧
      (∀ S ∈ D, S ∈ tube ρ' → S ∈ boxO ε R0) ∧
      (∀ S ∈ R₂, ρ' S < ‖piR3 S‖) := by
  obtain ⟨ρ₀, hρ₀, hsheet⟩ := sheet_geometry
  obtain ⟨hinj, hfl⟩ := hsheet ρ₀ hρ₀ le_rfl
  have hR0 : 0 < ρ₀ := hρ₀
  obtain ⟨εs, hεs, hshell⟩ := exists_shell_free R hRc hRF (ρ₀ / 2) ρ₀ (by positivity)
  have hε : 0 < min ρ₀ εs := lt_min hρ₀ hεs
  set ε := min ρ₀ εs with hεdef
  have hboxsub : boxC ε ρ₀ ⊆ boxC ρ₀ ρ₀ := fun S hS =>
    ⟨Metric.closedBall_subset_closedBall (min_le_left _ _) hS.1, hS.2⟩
  have hinj' : ∀ g : principalSix, g ≠ 1 → Disjoint (g • boxC ε ρ₀) (boxC ε ρ₀) := fun g hg =>
    (hinj g hg).mono (Set.smul_set_mono hboxsub) hboxsub
  have hfl' : ∀ g : principalSix, g ≠ 1 → Disjoint (g • boxC ε ρ₀) flat := fun g hg =>
    (hfl g hg).mono_left (Set.smul_set_mono hboxsub)
  -- the shell
  let M : Set Space := boxC ε ρ₀ ∩ {S | ρ₀ / 2 ≤ ‖(coordHomeo S).2‖}
  have hMc : IsCompact M := by
    refine (isCompact_boxC ε ρ₀).inter_right ?_
    exact isClosed_le continuous_const (continuous_norm.comp (continuous_snd.comp coordHomeo.continuous))
  have hRM : ∀ S ∈ R, S ∉ M := by
    rintro S hS ⟨hSb, hSt⟩
    refine hshell S hS ?_ hSt ?_
    · have : ‖(coordHomeo S).1‖ ≤ ε := by simpa [dist_zero_right] using hSb.1
      exact this.trans (min_le_right _ _)
    · simpa [dist_zero_right] using hSb.2
  -- the closed set the tube must avoid
  let N : Set Space := ((R ∩ (boxO ε ρ₀)ᶜ) ∪ R₂) ∪ ⋃ g ∈ {g : principalSix | g ≠ 1}, g • boxC ε ρ₀
  have hNc : IsClosed N :=
    ((hRc.inter (isOpen_boxO ε ρ₀).isClosed_compl).union hR₂c).union
      (isClosed_biUnion_smul_compact _ (isCompact_boxC ε ρ₀) _)
  have hNF : ∀ S ∈ N, S ∉ flat := by
    rintro S ((⟨hSR, hSb⟩ | hS2) | hS3) hSf
    · exact hSb (hRF S hSR hSf ▸ p0_mem_boxO hε hR0)
    · exact hR₂F S hS2 hSf
    · obtain ⟨g, hg, hSg⟩ := Set.mem_iUnion₂.mp hS3
      exact Set.disjoint_left.mp (hfl' g hg) hSg hSf
  obtain ⟨ρ', hρc, hρpos, hρε, hρN, hρfin⟩ := tube_proper (ε / 2) (half_pos hε) N hNc hNF
  have hZc : IsClosed (tube ρ') := isClosed_tube hρc
  have hfinZ := tube_finite_inv hρfin
  -- the neighbourhood of the retract
  let Y : Set Space := tube ρ' ∩ (boxO ε ρ₀)ᶜ
  have hYc : IsClosed Y := hZc.inter (isOpen_boxO ε ρ₀).isClosed_compl
  have hG2 : IsClosed (⋃ g : principalSix, g • Y) := by
    have := isClosed_biUnion_smul Y hYc (fun L hL => (hfinZ L hL).subset
      (fun g ⟨y, hy, hyL⟩ => ⟨y, Set.smul_set_mono Set.inter_subset_left hy, hyL⟩)) Set.univ
    simpa using this
  have hG1 : IsClosed (⋃ g : principalSix, g • M) := isClosed_saturation M hMc
  refine ⟨ε, ρ₀, ρ₀ / 2, ρ', ((⋃ g : principalSix, g • M) ∪ (⋃ g : principalSix, g • Y))ᶜ,
    hε, by positivity, by linarith, hρc, hρpos, (fun S => lt_of_le_of_lt (hρε S) (by linarith)),
    hinj', ?_, hρfin,
    (hG1.union hG2).isOpen_compl, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [Set.disjoint_left]
    intro S hS hSZ
    have := hρN S (Or.inr (Set.mem_iUnion₂.mpr ⟨g, hg, hS⟩))
    exact absurd hSZ (not_le.mpr this)
  · intro g S hS hgS
    apply hS
    rcases hgS with h | h
    · exact Or.inl ((smul_mem_saturation_iff g M S).mp h)
    · exact Or.inr ((smul_mem_saturation_iff g Y S).mp h)
  · intro S hS hSD
    rcases hSD with h | h
    · obtain ⟨g, hg⟩ := Set.mem_iUnion.mp h
      have hm := Set.mem_smul_set_iff_inv_smul_mem.mp hg
      exact hRM _ (hRG g⁻¹ S hS) hm
    · obtain ⟨g, hg⟩ := Set.mem_iUnion.mp h
      have hm := Set.mem_smul_set_iff_inv_smul_mem.mp hg
      have hmR := hRG g⁻¹ S hS
      have := hρN _ (Or.inl (Or.inl ⟨hmR, hm.2⟩))
      exact absurd hm.1 (not_le.mpr this)
  · intro S hS hSb
    by_contra hcon
    have hlt : ¬ ρ₀ / 2 ≤ ‖(coordHomeo S).2‖ := fun h => by
      apply hS
      left
      refine Set.mem_iUnion.mpr ⟨1, ?_⟩
      rw [one_smul]
      exact ⟨boxO_subset_boxC ε ρ₀ hSb, h⟩
    exact hcon (not_le.mp hlt)
  · intro S hS hSZ
    by_contra hcon
    apply hS
    right
    refine Set.mem_iUnion.mpr ⟨1, ?_⟩
    rw [one_smul]
    exact ⟨hSZ, hcon⟩
  · intro S hS
    exact hρN S (Or.inl (Or.inr hS))

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
