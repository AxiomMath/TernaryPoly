module

public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Basic

@[expose] public section


/-!
# Free resolutions from graded data on a single set

Original work by Claude Opus 5.5.

A free resolution of `ℂ` of length three is assembled from an augmented chain complex of
permutation modules carried by a single `Λ`-set `X`: every cell has a grade `0, …, 3`, the
boundary `δ` lowers the grade by one, and the augmentation `ε` lives on grade zero. The modules
of the resolution are the chains on the cells of each grade, the boundaries are the graded
pieces of `δ`, and exactness of the graded complex follows from exactness of `δ` against `ε`
because `δ` respects the grading.
-/

noncomputable section

namespace TernaryPeriodPolynomials.FreeResolution

open TernaryPeriodPolynomials.TopVanishing

/-- An augmented graded chain complex of permutation modules supported on a single `Λ`-set:
cells `X` of grade `0, …, 3`, a boundary `δ` lowering the grade by one, and an augmentation `ε`
on grade zero. -/
structure GradedComplexData (Λ : Type) [Group Λ] where
  /-- The cells. -/
  X : Type
  /-- The action on the cells. -/
  [action : MulAction Λ X]
  /-- The grade (dimension) of a cell. -/
  grade : X → ℕ
  grade_smul : ∀ (γ : Λ) (x : X), grade (γ • x) = grade x
  /-- The boundary on all chains. -/
  δ : (X →₀ ℂ) →ₗ[ℂ] (X →₀ ℂ)
  δ_equivariant : Equivariant Λ δ
  δ_δ : δ ∘ₗ δ = 0
  δ_grade : ∀ x y : X, y ∈ (δ (Finsupp.single x 1)).support → grade y + 1 = grade x
  /-- The augmentation. -/
  ε : (X →₀ ℂ) →ₗ[ℂ] ℂ
  ε_invariant : ∀ (γ : Λ) (z : X →₀ ℂ), ε (chainAct Λ γ z) = ε z
  ε_δ : ε ∘ₗ δ = 0
  ε_grade : ∀ x : X, grade x ≠ 0 → ε (Finsupp.single x 1) = 0
  free : ∀ (γ : Λ) (x : X), γ • x = x → γ = 1
  grade_le : ∀ x : X, grade x ≤ 3
  exact : ∀ z : X →₀ ℂ, δ z = 0 → ε z = 0 → ∃ y, δ y = z
  surj : ∃ x : X, ε (Finsupp.single x 1) ≠ 0

attribute [instance] GradedComplexData.action

/-- The coefficient of a translated chain. -/
theorem chainAct_apply {Λ S : Type} [Group Λ] [MulAction Λ S] (γ : Λ) (w : S →₀ ℂ) (y : S) :
    chainAct Λ γ w y = w (γ⁻¹ • y) := by
  have hy : y = γ • (γ⁻¹ • y) := (smul_inv_smul γ y).symm
  conv_lhs => rw [hy]
  rw [chainAct, Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective γ) w _

namespace GradedComplexData

variable {Λ : Type} [Group Λ] (D : GradedComplexData Λ)

/-- The cells of grade `k`. -/
abbrev Graded (k : ℕ) : Type := {x : D.X // D.grade x = k}

instance gradedAction (k : ℕ) : MulAction Λ (D.Graded k) where
  smul γ x := ⟨γ • x.1, by rw [D.grade_smul]; exact x.2⟩
  one_smul x := Subtype.ext (one_smul Λ x.1)
  mul_smul γ γ' x := Subtype.ext (mul_smul γ γ' x.1)

theorem graded_smul_val (k : ℕ) (γ : Λ) (x : D.Graded k) : (γ • x).1 = γ • x.1 := rfl

/-- Chains of grade `k` viewed as chains on all cells. -/
def incl (k : ℕ) : (D.Graded k →₀ ℂ) →ₗ[ℂ] (D.X →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ Subtype.val

/-- The grade-`k` part of a chain. -/
def proj (k : ℕ) : (D.X →₀ ℂ) →ₗ[ℂ] (D.Graded k →₀ ℂ) where
  toFun w := w.subtypeDomain (fun x => D.grade x = k)
  map_add' _ _ := Finsupp.subtypeDomain_add
  map_smul' c w := by
    ext x
    simp only [Finsupp.subtypeDomain_apply, Finsupp.smul_apply, RingHom.id_apply]

theorem proj_apply (k : ℕ) (w : D.X →₀ ℂ) (x : D.Graded k) : D.proj k w x = w x.1 :=
  Finsupp.subtypeDomain_apply

theorem incl_single (k : ℕ) (x : D.Graded k) (a : ℂ) :
    D.incl k (Finsupp.single x a) = Finsupp.single x.1 a := by
  rw [incl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem proj_incl (k : ℕ) (z : D.Graded k →₀ ℂ) : D.proj k (D.incl k z) = z := by
  ext x
  rw [proj_apply, incl, Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective z x

/-- A chain is homogeneous of grade `k`. -/
def Homogeneous (k : ℕ) (w : D.X →₀ ℂ) : Prop := ∀ y ∈ w.support, D.grade y = k

theorem incl_proj {k : ℕ} {w : D.X →₀ ℂ} (hw : D.Homogeneous k w) :
    D.incl k (D.proj k w) = w := by
  ext y
  rw [incl, Finsupp.lmapDomain_apply]
  by_cases hy : D.grade y = k
  · have e := Finsupp.mapDomain_apply_of_injective Subtype.val_injective (D.proj k w) ⟨y, hy⟩
    rw [e, proj_apply]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨x, rfl⟩; exact hy x.2)]
    by_contra h
    exact hy (hw y (Finsupp.mem_support_iff.mpr (Ne.symm h)))

theorem homogeneous_zero (k : ℕ) : D.Homogeneous k 0 := by
  intro y hy
  simp at hy

theorem Homogeneous.add {k : ℕ} {w w' : D.X →₀ ℂ} (hw : D.Homogeneous k w)
    (hw' : D.Homogeneous k w') : D.Homogeneous k (w + w') := by
  classical
  intro y hy
  rcases Finset.mem_union.mp (Finsupp.support_add hy) with h | h
  · exact hw y h
  · exact hw' y h

theorem Homogeneous.smul {k : ℕ} {w : D.X →₀ ℂ} (hw : D.Homogeneous k w) (c : ℂ) :
    D.Homogeneous k (c • w) := fun y hy => hw y (Finsupp.support_smul hy)

theorem homogeneous_δ_single (x : D.X) (a : ℂ) {k : ℕ} (hx : D.grade x = k + 1) :
    D.Homogeneous k (D.δ (Finsupp.single x a)) := by
  have e : Finsupp.single x a = a • Finsupp.single x (1 : ℂ) := by simp
  rw [e, map_smul]
  refine Homogeneous.smul D (fun y hy => ?_) a
  have := D.δ_grade x y hy
  omega

theorem homogeneous_δ_incl (k : ℕ) (z : D.Graded (k + 1) →₀ ℂ) :
    D.Homogeneous k (D.δ (D.incl (k + 1) z)) := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]; exact D.homogeneous_zero k
  | add f g hf hg => rw [map_add, map_add]; exact hf.add D hg
  | single x a => rw [incl_single]; exact D.homogeneous_δ_single x.1 a x.2

theorem δ_grade_zero (z : D.Graded 0 →₀ ℂ) : D.δ (D.incl 0 z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | single x a =>
    rw [incl_single]
    have e : Finsupp.single x.1 a = a • Finsupp.single x.1 (1 : ℂ) := by simp
    rw [e, map_smul]
    have h0 : D.δ (Finsupp.single x.1 1) = 0 := by
      ext y
      rw [Finsupp.zero_apply]
      by_contra h
      have := D.δ_grade x.1 y (Finsupp.mem_support_iff.mpr h)
      have h2 := x.2
      omega
    rw [h0, smul_zero]

theorem ε_incl_succ (k : ℕ) (z : D.Graded (k + 1) →₀ ℂ) : D.ε (D.incl (k + 1) z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | single x a =>
    rw [incl_single]
    have e : Finsupp.single x.1 a = a • Finsupp.single x.1 (1 : ℂ) := by simp
    rw [e, map_smul, D.ε_grade x.1 (by rw [x.2]; omega), smul_zero]

/-- The grade-`k` part of a boundary only sees the grade-`(k+1)` part of the chain. -/
theorem proj_δ (k : ℕ) (w : D.X →₀ ℂ) :
    D.proj k (D.δ w) = D.proj k (D.δ (D.incl (k + 1) (D.proj (k + 1) w))) := by
  classical
  induction w using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x a =>
    by_cases hx : D.grade x = k + 1
    · have e : D.proj (k + 1) (Finsupp.single x a) = Finsupp.single ⟨x, hx⟩ a := by
        ext y
        rw [proj_apply, Finsupp.single_apply, Finsupp.single_apply]
        by_cases h : x = y.1
        · rw [ite_eq_left h, ite_eq_left (Subtype.ext h)]
        · rw [ite_eq_right h, ite_eq_right (fun h' => h (congrArg Subtype.val h'))]
      rw [e, incl_single]
    · have e : D.proj (k + 1) (Finsupp.single x a) = 0 := by
        ext y
        rw [proj_apply, Finsupp.single_apply,
          ite_eq_right (fun h => hx (by rw [h]; exact y.2)), Finsupp.zero_apply]
      rw [e, map_zero, map_zero, map_zero]
      ext y
      rw [proj_apply, Finsupp.zero_apply]
      by_contra h
      have hmem : y.1 ∈ (D.δ (Finsupp.single x a)).support := Finsupp.mem_support_iff.mpr h
      have e1 : Finsupp.single x a = a • Finsupp.single x (1 : ℂ) := by simp
      rw [e1, map_smul] at hmem
      have := D.δ_grade x y.1 (Finsupp.support_smul hmem)
      have h2 := y.2
      omega

theorem incl_chainAct (k : ℕ) (γ : Λ) (z : D.Graded k →₀ ℂ) :
    D.incl k (chainAct Λ γ z) = chainAct Λ γ (D.incl k z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x a =>
    rw [chainAct_single, incl_single, incl_single, chainAct_single, graded_smul_val]

theorem proj_chainAct (k : ℕ) (γ : Λ) (w : D.X →₀ ℂ) :
    D.proj k (chainAct Λ γ w) = chainAct Λ γ (D.proj k w) := by
  ext x
  rw [proj_apply, chainAct_apply, chainAct_apply, proj_apply]
  rfl

/-- The cells of the resolution: a point in index `0` and the cells of grade `k` in index
`k + 1`. -/
def cell : ℕ → Type
  | 0 => Unit
  | k + 1 => D.Graded k

/-- The action on the cells of the resolution. -/
instance cellAction : ∀ k, MulAction Λ (D.cell k)
  | 0 => inferInstanceAs (MulAction Λ Unit)
  | k + 1 => inferInstanceAs (MulAction Λ (D.Graded k))

/-- The augmentation `ε` on grade-zero chains, with values in chains on the point. -/
def augmentation : (D.Graded 0 →₀ ℂ) →ₗ[ℂ] (Unit →₀ ℂ) :=
  (D.ε ∘ₗ D.incl 0).smulRight (Finsupp.single () 1)

/-- The boundaries of the resolution. -/
def boundary : ∀ k, (D.cell (k + 1) →₀ ℂ) →ₗ[ℂ] (D.cell k →₀ ℂ)
  | 0 => D.augmentation
  | k + 1 => D.proj k ∘ₗ D.δ ∘ₗ D.incl (k + 1)

theorem equivariant_zero_aux (γ : Λ) (z : D.Graded 0 →₀ ℂ) :
    D.ε (D.incl 0 (chainAct Λ γ z)) • (Finsupp.single () 1 : Unit →₀ ℂ) =
      chainAct Λ γ (D.ε (D.incl 0 z) • (Finsupp.single () 1 : Unit →₀ ℂ)) := by
  rw [incl_chainAct, D.ε_invariant, map_smul, chainAct_single]

theorem equivariant_succ_aux (k : ℕ) (γ : Λ) (z : D.Graded (k + 1) →₀ ℂ) :
    D.proj k (D.δ (D.incl (k + 1) (chainAct Λ γ z))) =
      chainAct Λ γ (D.proj k (D.δ (D.incl (k + 1) z))) := by
  rw [incl_chainAct, D.δ_equivariant.apply, proj_chainAct]

theorem boundary_equivariant : ∀ k, Equivariant Λ (D.boundary k)
  | 0 => fun γ => LinearMap.ext fun z => D.equivariant_zero_aux γ z
  | k + 1 => fun γ => LinearMap.ext fun z => D.equivariant_succ_aux k γ z

theorem comp_zero_aux (z : D.Graded (0 + 1) →₀ ℂ) :
    D.ε (D.incl 0 (D.proj 0 (D.δ (D.incl (0 + 1) z)))) • (Finsupp.single () 1 : Unit →₀ ℂ) =
      0 := by
  rw [incl_proj D (D.homogeneous_δ_incl 0 z)]
  have := LinearMap.congr_fun D.ε_δ (D.incl (0 + 1) z)
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at this
  rw [this, zero_smul]

theorem comp_succ_aux (k : ℕ) (z : D.Graded (k + 1 + 1) →₀ ℂ) :
    D.proj k (D.δ (D.incl (k + 1) (D.proj (k + 1) (D.δ (D.incl (k + 1 + 1) z))))) = 0 := by
  rw [incl_proj D (D.homogeneous_δ_incl (k + 1) z)]
  have := LinearMap.congr_fun D.δ_δ (D.incl (k + 1 + 1) z)
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at this
  rw [this, map_zero]

theorem boundary_comp : ∀ k, D.boundary k ∘ₗ D.boundary (k + 1) = 0
  | 0 => LinearMap.ext fun z => D.comp_zero_aux z
  | k + 1 => LinearMap.ext fun z => D.comp_succ_aux k z

theorem boundary_zero_surjective : LinearMap.range (D.boundary 0) = ⊤ := by
  obtain ⟨x, hx⟩ := D.surj
  have hg : D.grade x = 0 := by
    by_contra h
    exact hx (D.ε_grade x h)
  rw [LinearMap.range_eq_top]
  intro w
  refine ⟨(w () / D.ε (Finsupp.single x 1)) •
    (Finsupp.single (⟨x, hg⟩ : D.Graded 0) 1 : D.Graded 0 →₀ ℂ), ?_⟩
  have key : D.ε (D.incl 0 ((w () / D.ε (Finsupp.single x 1)) •
      Finsupp.single (⟨x, hg⟩ : D.Graded 0) 1)) • (Finsupp.single () 1 : Unit →₀ ℂ) = w := by
    rw [map_smul, incl_single, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
    refine Finsupp.unique_ext ?_
    show (w () • Finsupp.single () (1 : ℂ)) () = w ()
    rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  exact key

theorem boundary_exact : ∀ k,
    LinearMap.ker (D.boundary k) ≤ LinearMap.range (D.boundary (k + 1))
  | 0 => by
    intro z hz
    have hz' : D.ε (D.incl 0 z) • (Finsupp.single () 1 : Unit →₀ ℂ) = 0 :=
      LinearMap.mem_ker.mp hz
    have hε : D.ε (D.incl 0 z) = 0 := by
      have := congrArg (fun w : Unit →₀ ℂ => w ()) hz'
      simpa using this
    obtain ⟨y, hy⟩ := D.exact (D.incl 0 z) (D.δ_grade_zero z) hε
    refine LinearMap.mem_range.mpr ⟨D.proj (0 + 1) y, ?_⟩
    show D.proj 0 (D.δ (D.incl (0 + 1) (D.proj (0 + 1) y))) = z
    rw [← proj_δ, hy]
    exact D.proj_incl 0 z
  | k + 1 => by
    intro z hz
    have hz' : D.proj k (D.δ (D.incl (k + 1) z)) = 0 := LinearMap.mem_ker.mp hz
    have hδ : D.δ (D.incl (k + 1) z) = 0 := by
      rw [← incl_proj D (D.homogeneous_δ_incl k z), hz', map_zero]
    obtain ⟨y, hy⟩ := D.exact (D.incl (k + 1) z) hδ (D.ε_incl_succ k z)
    refine LinearMap.mem_range.mpr ⟨D.proj (k + 1 + 1) y, ?_⟩
    show D.proj (k + 1) (D.δ (D.incl (k + 1 + 1) (D.proj (k + 1 + 1) y))) = z
    rw [← proj_δ, hy]
    exact D.proj_incl (k + 1) z

theorem graded_four_empty (x : D.Graded 4) : False := by
  have h1 := D.grade_le x.1
  have h2 := x.2
  omega

/-- The free resolution of length three determined by graded data. -/
def toFreeResolution : FreeResolution Λ 3 where
  cell := D.cell
  action := D.cellAction
  d := D.boundary
  equivariant := D.boundary_equivariant
  d_comp_d := D.boundary_comp
  point := inferInstanceAs (Unique Unit)
  free := by
    intro k γ s hs
    exact D.free γ s.1 (congrArg Subtype.val hs)
  exact := ⟨D.boundary_zero_surjective, D.boundary_exact⟩
  top := ⟨fun x => D.graded_four_empty x⟩

end GradedComplexData

end TernaryPeriodPolynomials.FreeResolution
