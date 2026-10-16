module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.PeterssonDomain
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Gamma.OneThreeBasic

@[expose] public section


/-!
# A fundamental domain for `Γ₁(3)`

The four matrices `1, S, ST, ST²` (`rep`) represent the right cosets of `Γ₀(3)` in `SL₂(ℤ)`: for
`x ∈ SL₂(ℤ)` exactly one `rᵢ x` has lower-left entry divisible by `3` (`exists_rep_mul`,
`rep_unique`; the bottom row of `rᵢ` runs over `ℙ¹(𝔽₃)`). Since `Γ₀(3) = ±Γ₁(3)`, the images of
`Γ₀(3)` and `Γ₁(3)` in `PGL(2,ℝ)` agree, so the union `𝒟₃ = ⋃ᵢ rᵢ 𝒟` of four translates of the
standard fundamental domain is a fundamental domain of the image `imageThree` of `Γ₁(3)`
(`fdThree_isFundamentalDomain`). It has finite hyperbolic volume (`volume_fdThree_lt_top`) and
contains `𝒟` (`fd_subset_fdThree`). The map `Γ₁(3) → PGL(2,ℝ)` is injective (`mk_eq_one`), as
`-1 ∉ Γ₁(3)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane Matrix MeasureTheory
open scoped MatrixGroups Pointwise

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonDomain

open TernaryPeriodPolynomials.Spectral.PeterssonDomain
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

/-! ### Coset representatives of `Γ₀(3)` -/

/-- `S Tʲ = [[0, -1], [1, j]]`. -/
def shearS (j : Fin 3) : SL(2, ℤ) :=
  ⟨!![0, -1; 1, (j.val : ℤ)], by simp [Matrix.det_fin_two_of]⟩

/-- The coset representatives `1, S, ST, ST²` of `Γ₀(3)` in `SL₂(ℤ)`. -/
def rep : Option (Fin 3) → SL(2, ℤ)
  | none => 1
  | some j => shearS j

/-- The residue modulo `3` of the lower-left entry of `rᵢ x`, in terms of the first column
`(a, c)` of `x`. -/
def cond : Option (Fin 3) → ZMod 3 → ZMod 3 → ZMod 3
  | none, _, c => c
  | some j, a, c => a + (j.val : ZMod 3) * c

theorem rep_mul_10 (i : Option (Fin 3)) (x : SL(2, ℤ)) :
    (((rep i * x) 1 0 : ℤ) : ZMod 3) = cond i ((x 0 0 : ℤ) : ZMod 3) ((x 1 0 : ℤ) : ZMod 3) := by
  cases i with
  | none => simp [rep, cond]
  | some j =>
    change (((!![0, -1; 1, (j.val : ℤ)] * (x : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ℤ) : ZMod 3) = _
    simp [cond, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_cast (x : SL(2, ℤ)) :
    ((x 0 0 : ℤ) : ZMod 3) * ((x 1 1 : ℤ) : ZMod 3) -
      ((x 0 1 : ℤ) : ZMod 3) * ((x 1 0 : ℤ) : ZMod 3) = 1 := by
  have h := x.property
  rw [Matrix.det_fin_two] at h
  have h' := congrArg (Int.cast : ℤ → ZMod 3) h
  push_cast at h'
  exact h'

theorem col_ne (x : SL(2, ℤ)) :
    ¬(((x 0 0 : ℤ) : ZMod 3) = 0 ∧ ((x 1 0 : ℤ) : ZMod 3) = 0) := by
  rintro ⟨ha, hc⟩
  have h := det_cast x
  rw [ha, hc] at h
  simp at h

theorem cond_exists : ∀ a c : ZMod 3, ¬(a = 0 ∧ c = 0) → ∃ i, cond i a c = 0 := by decide

theorem cond_unique : ∀ a c : ZMod 3, ¬(a = 0 ∧ c = 0) → ∀ i j,
    cond i a c = 0 → cond j a c = 0 → i = j := by decide

/-- **Existence**: some `rᵢ x` lies in `Γ₀(3)`. -/
theorem exists_rep_mul (x : SL(2, ℤ)) : ∃ i, (((rep i * x) 1 0 : ℤ) : ZMod 3) = 0 := by
  obtain ⟨i, hi⟩ := cond_exists _ _ (col_ne x)
  exact ⟨i, by rw [rep_mul_10]; exact hi⟩

/-- **Uniqueness** of the index. -/
theorem rep_unique (x : SL(2, ℤ)) (i j : Option (Fin 3))
    (hi : (((rep i * x) 1 0 : ℤ) : ZMod 3) = 0) (hj : (((rep j * x) 1 0 : ℤ) : ZMod 3) = 0) :
    i = j := by
  rw [rep_mul_10] at hi hj
  exact cond_unique _ _ (col_ne x) i j hi hj

/-- An element of `Γ₀(3)` is `±` an element of `Γ₁(3)`. -/
theorem exists_gammaOne (η : SL(2, ℤ)) (h : ((η 1 0 : ℤ) : ZMod 3) = 0) :
    ∃ η' ∈ CongruenceSubgroup.Gamma1 3, psl η' = psl η := by
  have hdet : ((η 0 0 : ℤ) : ZMod 3) * ((η 1 1 : ℤ) : ZMod 3) = 1 := by
    have := det_cast η
    erw [h, mul_zero, sub_zero] at this
    exact this
  have key : ∀ a d : ZMod 3, a * d = 1 → (a = 1 ∧ d = 1) ∨ (a = -1 ∧ d = -1) := by decide
  rcases key _ _ hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · exact ⟨η, (CongruenceSubgroup.Gamma1_mem 3 η).mpr ⟨ha, hd, h⟩, rfl⟩
  · refine ⟨-η, (CongruenceSubgroup.Gamma1_mem 3 _).mpr ⟨?_, ?_, ?_⟩, psl_neg η⟩ <;>
      simp [ha, hd, h]
    all_goals rfl

theorem gammaOne_10 {η : SL(2, ℤ)} (h : η ∈ CongruenceSubgroup.Gamma1 3) :
    ((η 1 0 : ℤ) : ZMod 3) = 0 :=
  ((CongruenceSubgroup.Gamma1_mem 3 η).mp h).2.2

theorem neg_one_not_mem : (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 3 := by
  intro h
  have h1 := ((CongruenceSubgroup.Gamma1_mem 3 _).mp h).1
  simp at h1
  exact absurd h1 (by decide)

/-! ### The image of `Γ₁(3)` in `PGL(2,ℝ)` -/

/-- The image of `Γ₁(3)` in `PGL(2,ℝ)`. -/
abbrev imageThree : Subgroup PGL(2, ℝ) := binaryRealGammaOneThree.map ProjGenLinGroup.mk

theorem imageThree_eq : imageThree = (CongruenceSubgroup.Gamma1 3).map psl := by
  rw [imageThree, binaryRealGammaOneThree, Subgroup.map_map]
  rfl

theorem imageThree_le : imageThree ≤ modularImage := by
  rw [imageThree_eq]
  rintro _ ⟨γ, -, rfl⟩
  exact ⟨γ, rfl⟩

instance countable_imageThree : Countable imageThree := by
  rw [imageThree_eq]
  infer_instance

instance countable_gammaOneThree : Countable binaryRealGammaOneThree := by
  have := countable_SL
  have hc : (Set.range fun g : SL(2, ℤ) => SpecialLinearGroup.mapGL ℝ g).Countable :=
    Set.countable_range _
  apply Set.Countable.to_subtype
  apply hc.mono
  rintro _ ⟨g, -, rfl⟩
  exact ⟨g, rfl⟩

/-- **`Γ₁(3) → PGL(2,ℝ)` is injective.** -/
theorem mk_eq_one {γ : GL (Fin 2) ℝ} (hγ : γ ∈ binaryRealGammaOneThree)
    (h : ProjGenLinGroup.mk γ = 1) : γ = 1 := by
  obtain ⟨η, hη, rfl⟩ := hγ
  have h' : psl η = psl 1 := by
    rw [map_one]
    exact h
  rcases (psl_eq_iff _ _).mp h' with h1 | h1
  · rw [h1, map_one]
  · exact absurd (h1 ▸ hη) neg_one_not_mem

/-! ### The fundamental domain -/

/-- The fundamental domain `𝒟₃ = 𝒟 ∪ S𝒟 ∪ ST𝒟 ∪ ST²𝒟` of `Γ₁(3)`. -/
def fdThree : Set ℍ := ⋃ i, psl (rep i) • ModularGroup.fd

/-- **`𝒟₃` is a fundamental domain of `Γ₁(3)`.** -/
theorem fdThree_isFundamentalDomain : IsFundamentalDomain imageThree fdThree volume := by
  apply isFundamentalDomain_subgroup fd_isFundamentalDomain imageThree_le
    (fun i => psl (rep i)) (fun i => ⟨rep i, rfl⟩)
  · rintro _ ⟨γ, rfl⟩
    obtain ⟨i, hi⟩ := exists_rep_mul γ
    obtain ⟨η, hη, hηeq⟩ := exists_gammaOne _ hi
    refine ⟨i, psl η, ?_, ?_⟩
    · rw [imageThree_eq]
      exact ⟨η, hη, rfl⟩
    · rw [hηeq, map_mul, inv_mul_cancel_left]
  · intro i j h h' hh hh' heq
    rw [imageThree_eq] at hh hh'
    obtain ⟨η, hη, rfl⟩ := hh
    obtain ⟨η', hη', rfl⟩ := hh'
    have hrel : psl (rep j * (rep i)⁻¹) = psl (η' * η⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_inv]
      calc psl (rep j) * (psl (rep i))⁻¹
          = psl (rep j) * ((psl (rep i))⁻¹ * psl η) * (psl η)⁻¹ := by group
        _ = psl (rep j) * ((psl (rep j))⁻¹ * psl η') * (psl η)⁻¹ := by rw [heq]
        _ = psl η' * (psl η)⁻¹ := by group
    have hmem : η' * η⁻¹ ∈ CongruenceSubgroup.Gamma1 3 :=
      (CongruenceSubgroup.Gamma1 3).mul_mem hη' ((CongruenceSubgroup.Gamma1 3).inv_mem hη)
    have h10 : (((rep j * (rep i)⁻¹) 1 0 : ℤ) : ZMod 3) = 0 := by
      rcases (psl_eq_iff _ _).mp hrel with h1 | h1
      · rw [h1]
        exact gammaOne_10 hmem
      · rw [h1]
        have := gammaOne_10 hmem
        simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero]
        exact this
    have hi : (((rep i * (rep i)⁻¹) 1 0 : ℤ) : ZMod 3) = 0 := by simp
    have hij := rep_unique _ i j hi h10
    subst hij
    exact mul_left_cancel heq

theorem volume_fdThree_lt_top : volume fdThree < ⊤ := by
  calc volume fdThree ≤ ∑ i, volume (psl (rep i) • ModularGroup.fd) :=
        measure_iUnion_fintype_le _ _
    _ = ∑ _i : Option (Fin 3), volume ModularGroup.fd := by simp only [measure_smul]
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun _ _ => volume_fd_lt_top

instance : IsFiniteMeasure (volume.restrict fdThree) :=
  isFiniteMeasure_restrict.mpr volume_fdThree_lt_top.ne

theorem fd_subset_fdThree : ModularGroup.fd ⊆ fdThree := by
  intro z hz
  refine Set.mem_iUnion.mpr ⟨none, ?_⟩
  simpa [rep] using hz

end TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonDomain
