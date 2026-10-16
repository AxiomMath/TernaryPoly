module

public import TernaryPeriodPolynomials.Building.FreeResolution.Owner
public import TernaryPeriodPolynomials.Building.FreeResolution.Signs
public import TernaryPeriodPolynomials.Building.FreeResolution.Builder
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

@[expose] public section


/-!
# The well-rounded complex of `Γ(3)`

Original work by Claude Opus 5.5.

The cells are the spanning simplices `T` of the Voronoi complex (sets of lines minimal for a
common vertex that span `ℚ³`); the cell `T` has dimension `6 − |T|`. Its boundary inserts one
line, `δ T = ∑_w s(T, w) (T ∪ {w})`, with the label sign `s`; `δ ∘ δ = 0` because the two orders
of inserting two lines have opposite signs. The principal congruence subgroup `Γ(3)` acts on cells
by translating lines; it preserves labels, so `δ` commutes with the sign-free permutation action,
and it acts freely: a translation fixing a spanning set of minimal lines fixes each of them (they
have distinct labels), hence fixes three independent vectors (a sign is excluded modulo three).
-/

noncomputable section

namespace TernaryPeriodPolynomials.FreeResolution

open GeneralEisenstein Matrix TernaryPeriodPolynomials.TopVanishing
open scoped Pointwise

/-! ### Simplices and cells -/

theorem IsSimplex.mono {T T' : Finset Line} (h : IsSimplex T') (hT : T ⊆ T') : IsSimplex T := by
  obtain ⟨v, hv⟩ := h
  exact ⟨v, hT.trans hv⟩

theorem IsSimplex.label_injOn {T : Finset Line} (h : IsSimplex T) :
    Set.InjOn Line.label (T : Set Line) := by
  obtain ⟨v, hv⟩ := h
  exact v.label_injOn.mono (Finset.coe_subset.mpr hv)

/-- A label of a line outside a simplex containing both is not a label of the simplex. -/
theorem label_not_mem_of_simplex {T : Finset Line} {w : Line} (h : IsSimplex (insert w T))
    (hw : w ∉ T) : w.label ∉ T.image Line.label := by
  intro hmem
  obtain ⟨t, ht, hlt⟩ := Finset.mem_image.mp hmem
  have := h.label_injOn (Finset.mem_coe.mpr (Finset.mem_insert_of_mem ht))
    (Finset.mem_coe.mpr (Finset.mem_insert_self w T)) hlt
  exact hw (by rw [← this]; exact ht)

/-- A cell: a spanning simplex. -/
def IsCell (T : Finset Line) : Prop := Spans T ∧ IsSimplex T

/-! ### The neighbours of a set of lines -/

open Classical in
/-- The lines whose insertion into `T` still gives a simplex. -/
def nbrs (T : Finset Line) : Finset Line :=
  if h : Spans T then ((vertSet_finite h).toFinset.biUnion Vtx.M).filter (· ∉ T) else ∅

theorem mem_nbrs {T : Finset Line} (hT : Spans T) (w : Line) :
    w ∈ nbrs T ↔ w ∉ T ∧ IsSimplex (insert w T) := by
  rw [nbrs, dite_eq_left hT, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨B, hB, hw⟩, hwT⟩
    have hB' : T ⊆ B.M := (Set.Finite.mem_toFinset _).mp hB
    exact ⟨hwT, B, Finset.insert_subset hw hB'⟩
  · rintro ⟨hwT, B, hB⟩
    exact ⟨⟨B, (Set.Finite.mem_toFinset _).mpr ((Finset.subset_insert w T).trans hB),
      hB (Finset.mem_insert_self w T)⟩, hwT⟩

theorem nbrs_of_not_spans {T : Finset Line} (hT : ¬ Spans T) : nbrs T = ∅ := by
  rw [nbrs, dite_eq_right hT]

/-! ### The coboundary on all finite sets of lines -/

/-- The coboundary of a single set of lines. -/
def coboundaryOf (T : Finset Line) : Finset Line →₀ ℂ :=
  ∑ w ∈ nbrs T, insSign T w • Finsupp.single (insert w T) 1

/-- The coboundary on chains of finite sets of lines. -/
def δF : (Finset Line →₀ ℂ) →ₗ[ℂ] (Finset Line →₀ ℂ) := Finsupp.linearCombination ℂ coboundaryOf

theorem δF_single (T : Finset Line) : δF (Finsupp.single T 1) = coboundaryOf T := by
  rw [δF, Finsupp.linearCombination_single, one_smul]

theorem δF_coboundaryOf (T : Finset Line) : δF (coboundaryOf T) = 0 := by
  by_cases hT : Spans T
  swap
  · rw [coboundaryOf, nbrs_of_not_spans hT, Finset.sum_empty, map_zero]
  have e : δF (coboundaryOf T) = ∑ p ∈ (nbrs T).sigma (fun w => nbrs (insert w T)),
      (insSign T p.1 * insSign (insert p.1 T) p.2) •
        Finsupp.single (insert p.2 (insert p.1 T)) (1 : ℂ) := by
    rw [coboundaryOf, map_sum, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_smul, δF_single, coboundaryOf, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [smul_smul]
  rw [e]
  have key : ∀ p ∈ (nbrs T).sigma (fun w => nbrs (insert w T)),
      p.1 ∉ T ∧ p.2 ∉ insert p.1 T ∧ IsSimplex (insert p.2 (insert p.1 T)) := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_sigma.mp hp
    obtain ⟨h1a, -⟩ := (mem_nbrs hT _).mp h1
    have hT' : Spans (insert p.1 T) := hT.mono (Finset.subset_insert _ _)
    obtain ⟨h2a, h2b⟩ := (mem_nbrs hT' _).mp h2
    exact ⟨h1a, h2a, h2b⟩
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := key p hp
    have hne : p.2 ≠ p.1 := fun h => h2 (by rw [h]; exact Finset.mem_insert_self _ _)
    have h2T : p.2 ∉ T := fun h => h2 (Finset.mem_insert_of_mem h)
    have hcomm : insert p.1 (insert p.2 T) = insert p.2 (insert p.1 T) := Finset.insert_comm _ _ _
    have hS1 : IsSimplex (insert p.1 T) := h3.mono (Finset.subset_insert _ _)
    have hS2 : IsSimplex (insert p.2 T) :=
      h3.mono (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
    have hl1 := label_not_mem_of_simplex hS1 h1
    have hl2 := label_not_mem_of_simplex hS2 h2T
    have hl12 : p.1.label ≠ p.2.label := by
      intro h
      apply hne
      exact (h3.label_injOn (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) h.symm)
    show (insSign T p.1 * insSign (insert p.1 T) p.2) •
        Finsupp.single (insert p.2 (insert p.1 T)) (1 : ℂ) +
      (insSign T p.2 * insSign (insert p.2 T) p.1) •
        Finsupp.single (insert p.1 (insert p.2 T)) (1 : ℂ) = 0
    rw [hcomm, ← add_smul, insSign_swap T hl1 hl2 hl12, neg_add_cancel, zero_smul]
  · intro p hp _ h
    obtain ⟨-, h2, -⟩ := key p hp
    apply h2
    have : p.2 = p.1 := congrArg Sigma.fst h
    rw [this]
    exact Finset.mem_insert_self _ _
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := key p hp
    have h2T : p.2 ∉ T := fun h => h2 (Finset.mem_insert_of_mem h)
    have hne : p.1 ≠ p.2 := fun h => h2 (by rw [← h]; exact Finset.mem_insert_self _ _)
    refine Finset.mem_sigma.mpr ⟨(mem_nbrs hT _).mpr ⟨h2T, h3.mono
      (Finset.insert_subset_insert _ (Finset.subset_insert _ _))⟩, ?_⟩
    have hT' : Spans (insert p.2 T) := hT.mono (Finset.subset_insert _ _)
    refine (mem_nbrs hT' _).mpr ⟨?_, ?_⟩
    · intro hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hne h
      · exact h1 h
    · rw [Finset.insert_comm]
      exact h3
  · intro p _
    rfl

theorem δF_δF : δF ∘ₗ δF = 0 := by
  apply Finsupp.lhom_ext
  intro T a
  have e : Finsupp.single T a = a • Finsupp.single T (1 : ℂ) := by simp
  rw [LinearMap.comp_apply, LinearMap.zero_apply, e, map_smul, map_smul, δF_single,
    δF_coboundaryOf, smul_zero]

/-! ### The action of `Γ(3)` -/

theorem indep_level_smul (γ : principalLevel) (a b c : Line) :
    Line.Indep (γ • a) (γ • b) (γ • c) ↔ Line.Indep a b c := by
  simp only [level_smul]
  exact Line.indep_smul _ a b c

theorem spans_smul_of (γ : principalLevel) {T : Finset Line} (h : Spans T) : Spans (γ • T) := by
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := h
  exact ⟨γ • a, Finset.smul_mem_smul_finset ha, γ • b, Finset.smul_mem_smul_finset hb,
    γ • c, Finset.smul_mem_smul_finset hc, (indep_level_smul γ a b c).mpr habc⟩

theorem spans_smul (γ : principalLevel) (T : Finset Line) : Spans (γ • T) ↔ Spans T := by
  refine ⟨fun h => ?_, spans_smul_of γ⟩
  have := spans_smul_of γ⁻¹ h
  rwa [inv_smul_smul γ T] at this

theorem isSimplex_smul_of (γ : principalLevel) {T : Finset Line} (h : IsSimplex T) :
    IsSimplex (γ • T) := by
  obtain ⟨v, hv⟩ := h
  refine ⟨Vtx.translate (levelLift γ) v, ?_⟩
  rw [Vtx.translate_M]
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Finset.mem_smul_finset.mp hx
  exact Finset.mem_image.mpr ⟨t, hv ht, (level_smul γ t).symm⟩

theorem isSimplex_smul (γ : principalLevel) (T : Finset Line) :
    IsSimplex (γ • T) ↔ IsSimplex T := by
  refine ⟨fun h => ?_, isSimplex_smul_of γ⟩
  have := isSimplex_smul_of γ⁻¹ h
  rwa [inv_smul_smul γ T] at this

theorem isCell_smul (γ : principalLevel) (T : Finset Line) : IsCell (γ • T) ↔ IsCell T := by
  rw [IsCell, IsCell, spans_smul, isSimplex_smul]

theorem card_level_smul (γ : principalLevel) (T : Finset Line) : (γ • T).card = T.card := by
  rw [Finset.smul_finset_def, Finset.card_image_of_injective _ (MulAction.injective γ)]

theorem image_label_smul (γ : principalLevel) (T : Finset Line) :
    (γ • T).image Line.label = T.image Line.label := by
  rw [Finset.smul_finset_def, Finset.image_image]
  congr 1
  funext ℓ
  exact label_level_smul γ ℓ

theorem insSign_smul (γ : principalLevel) (T : Finset Line) (w : Line) :
    insSign (γ • T) (γ • w) = insSign T w := by
  rw [insSign, insSign, image_label_smul, label_level_smul]

theorem nbrs_smul (γ : principalLevel) (T : Finset Line) : nbrs (γ • T) = γ • nbrs T := by
  by_cases hT : Spans T
  · have hT' : Spans (γ • T) := (spans_smul γ T).mpr hT
    ext w
    rw [mem_nbrs hT', ← smul_inv_smul γ w, Finset.smul_mem_smul_finset_iff,
      Finset.smul_mem_smul_finset_iff, mem_nbrs hT, ← Finset.smul_finset_insert, isSimplex_smul]
  · rw [nbrs_of_not_spans hT, nbrs_of_not_spans (fun h => hT ((spans_smul γ T).mp h)),
      Finset.smul_finset_empty]

theorem coboundaryOf_smul (γ : principalLevel) (T : Finset Line) :
    coboundaryOf (γ • T) = chainAct principalLevel γ (coboundaryOf T) := by
  unfold coboundaryOf
  rw [nbrs_smul,
    show γ • nbrs T = (nbrs T).image (γ • ·) from Finset.smul_finset_def,
    Finset.sum_image (by
      intro a _ b _ h
      exact MulAction.injective γ h), map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, chainAct_single, insSign_smul, Finset.smul_finset_insert]

theorem δF_equivariant : Equivariant principalLevel δF := by
  apply equivariant_of_single
  intro γ T
  rw [δF_single, δF_single, coboundaryOf_smul]

/-! ### Freeness -/

/-- A vector orthogonal to three independent vectors vanishes (Cramer's rule). -/
theorem eq_zero_of_dots {x y z r : Vec} (hd : det3v x y z ≠ 0)
    (hx : ∑ l, r l * x l = 0) (hy : ∑ l, r l * y l = 0) (hz : ∑ l, r l * z l = 0) :
    ∀ l, r l = 0 := by
  simp only [Fin.sum_univ_three] at hx hy hz
  have e0 : det3v x y z * r 0 = (r 0 * x 0 + r 1 * x 1 + r 2 * x 2) * (y 1 * z 2 - y 2 * z 1) +
      (r 0 * y 0 + r 1 * y 1 + r 2 * y 2) * (z 1 * x 2 - z 2 * x 1) +
      (r 0 * z 0 + r 1 * z 1 + r 2 * z 2) * (x 1 * y 2 - x 2 * y 1) := by
    unfold det3v
    ring
  have e1 : det3v x y z * r 1 = (r 0 * x 0 + r 1 * x 1 + r 2 * x 2) * (y 2 * z 0 - y 0 * z 2) +
      (r 0 * y 0 + r 1 * y 1 + r 2 * y 2) * (z 2 * x 0 - z 0 * x 2) +
      (r 0 * z 0 + r 1 * z 1 + r 2 * z 2) * (x 2 * y 0 - x 0 * y 2) := by
    unfold det3v
    ring
  have e2 : det3v x y z * r 2 = (r 0 * x 0 + r 1 * x 1 + r 2 * x 2) * (y 0 * z 1 - y 1 * z 0) +
      (r 0 * y 0 + r 1 * y 1 + r 2 * y 2) * (z 0 * x 1 - z 1 * x 0) +
      (r 0 * z 0 + r 1 * z 1 + r 2 * z 2) * (x 0 * y 1 - x 1 * y 0) := by
    unfold det3v
    ring
  rw [hx, hy, hz] at e0 e1 e2
  simp only [zero_mul, add_zero] at e0 e1 e2
  intro l
  fin_cases l
  · exact (mul_eq_zero.mp e0).resolve_left hd
  · exact (mul_eq_zero.mp e1).resolve_left hd
  · exact (mul_eq_zero.mp e2).resolve_left hd

theorem eq_one_of_fix3 (k : IntegralGL3) {x y z : Vec} (hd : det3v x y z ≠ 0)
    (hx : mv k x = x) (hy : mv k y = y) (hz : mv k z = z) : k = 1 := by
  have hrow : ∀ i l, (k : Matrix (Fin 3) (Fin 3) ℤ) i l = if i = l then 1 else 0 := by
    intro i
    have hdot : ∀ w : Vec, mv k w = w →
        ∑ l, ((k : Matrix (Fin 3) (Fin 3) ℤ) i l - if i = l then 1 else 0) * w l = 0 := by
      intro w hw
      have h1 : ∑ l, (k : Matrix (Fin 3) (Fin 3) ℤ) i l * w l = w i := congrFun hw i
      simp [sub_mul, Finset.sum_sub_distrib, ite_mul, h1]
    have := eq_zero_of_dots hd (hdot x hx) (hdot y hy) (hdot z hz)
    intro l
    exact sub_eq_zero.mp (this l)
  apply Units.ext
  ext i l
  rw [hrow, Units.val_one, Matrix.one_apply]

theorem zmod3_eq_neg_self {y : Fin 3 → ZMod 3} (h : y = -y) : y = 0 := by
  have key : ∀ a : ZMod 3, a = -a → a = 0 := by decide
  funext i
  exact key (y i) (congrFun h i)

/-- `Γ(3)` acts freely on cells. -/
theorem eq_one_of_smul_eq (γ : principalLevel) {T : Finset Line} (hT : IsCell T)
    (h : γ • T = T) : γ = 1 := by
  obtain ⟨⟨a, ha, b, hb, c, hc, habc⟩, v, hv⟩ := hT
  have hfix : ∀ t ∈ T, γ • t = t := by
    intro t ht
    have hmem : γ • t ∈ T := by
      rw [← h]
      exact Finset.smul_mem_smul_finset ht
    exact v.label_injOn (Finset.mem_coe.mpr (hv hmem)) (Finset.mem_coe.mpr (hv ht))
      (label_level_smul γ t)
  have hvec : ∀ t ∈ T, mv (levelLift γ) (Quotient.out t) = Quotient.out t := by
    intro t ht
    have h1 := hfix t ht
    rw [level_smul, ← Line.mk_out t, smul_mk] at h1
    rcases Line.mk_eq_mk.mp h1 with h2 | h2
    · exact h2.symm
    · exfalso
      have hred := red_mv_of_mem_ker (levelLift_mem_ker γ) (Quotient.out t)
      have h3 : mv (levelLift γ) (Quotient.out t) = -Quotient.out t := by
        have := congrArg Neg.neg h2
        rw [neg_neg] at this
        exact this.symm
      rw [h3, red_neg] at hred
      apply v.red_ne_zero_of_mem (x := Quotient.out t) (by rw [Line.mk_out]; exact hv ht)
      exact zmod3_eq_neg_self hred.symm
  have hk := eq_one_of_fix3 (levelLift γ) habc (hvec a ha) (hvec b hb) (hvec c hc)
  have h1 := integralToRational_levelLift γ
  rw [hk, map_one] at h1
  exact Subtype.ext h1.symm

/-! ### Cells -/

/-- The cells of the well-rounded complex. -/
@[ext] structure Cell where
  /-- The minimal lines of the cell. -/
  val : Finset Line
  isCell : IsCell val

theorem Cell.val_injective : Function.Injective Cell.val := fun _ _ h => Cell.ext h

instance : MulAction principalLevel Cell where
  smul γ C := ⟨γ • C.val, (isCell_smul γ C.val).mpr C.isCell⟩
  one_smul C := Cell.ext (one_smul _ C.val)
  mul_smul γ γ' C := Cell.ext (mul_smul γ γ' C.val)

theorem Cell.smul_val (γ : principalLevel) (C : Cell) : (γ • C).val = γ • C.val := rfl

/-- Chains on cells as chains on sets of lines. -/
def toF : (Cell →₀ ℂ) →ₗ[ℂ] (Finset Line →₀ ℂ) := Finsupp.lmapDomain ℂ ℂ Cell.val

/-- The restriction of chains on sets of lines to cells. -/
def ofF : (Finset Line →₀ ℂ) →ₗ[ℂ] (Cell →₀ ℂ) := Finsupp.lcomapDomain Cell.val Cell.val_injective

theorem ofF_apply (w : Finset Line →₀ ℂ) (C : Cell) : ofF w C = w C.val := rfl

theorem toF_single (C : Cell) (a : ℂ) : toF (Finsupp.single C a) = Finsupp.single C.val a := by
  rw [toF, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem toF_apply_val (z : Cell →₀ ℂ) (C : Cell) : toF z C.val = z C := by
  rw [toF, Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_apply_of_injective Cell.val_injective z C

theorem ofF_toF (z : Cell →₀ ℂ) : ofF (toF z) = z := by
  ext C
  rw [ofF_apply, toF_apply_val]

theorem toF_injective : Function.Injective toF := fun z z' h => by
  rw [← ofF_toF z, ← ofF_toF z', h]

/-- A chain supported on cells. -/
def CellSupp (w : Finset Line →₀ ℂ) : Prop := ∀ T ∈ w.support, IsCell T

theorem toF_ofF {w : Finset Line →₀ ℂ} (hw : CellSupp w) : toF (ofF w) = w := by
  ext T
  by_cases hT : IsCell T
  · exact toF_apply_val (ofF w) ⟨T, hT⟩
  · rw [toF, Finsupp.lmapDomain_apply, Finsupp.mapDomain_of_notMem_range _ _ (by
      rintro ⟨C, rfl⟩
      exact hT C.isCell)]
    by_contra h
    exact hT (hw T (Finsupp.mem_support_iff.mpr (Ne.symm h)))

theorem cellSupp_coboundaryOf {T : Finset Line} (hT : Spans T) : CellSupp (coboundaryOf T) := by
  classical
  intro S hS
  obtain ⟨w, hw, hSw⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hS)
  have hS' := Finsupp.support_smul hSw
  rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hS'
  obtain ⟨-, hsimp⟩ := (mem_nbrs hT w).mp hw
  rw [hS']
  exact ⟨hT.mono (Finset.subset_insert _ _), hsimp⟩

theorem cellSupp_δF_toF (z : Cell →₀ ℂ) : CellSupp (δF (toF z)) := by
  classical
  intro S hS
  have e : δF (toF z) = ∑ C ∈ z.support, z C • coboundaryOf C.val := by
    conv_lhs => rw [← Finsupp.sum_single z]
    rw [Finsupp.sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [toF_single, ← Finsupp.smul_single_one, map_smul, δF_single]
  rw [e] at hS
  obtain ⟨C, -, hSC⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hS)
  exact cellSupp_coboundaryOf C.isCell.1 S (Finsupp.support_smul hSC)

/-- The boundary of the well-rounded complex. -/
def δC : (Cell →₀ ℂ) →ₗ[ℂ] (Cell →₀ ℂ) := ofF ∘ₗ δF ∘ₗ toF

theorem toF_δC (z : Cell →₀ ℂ) : toF (δC z) = δF (toF z) :=
  toF_ofF (cellSupp_δF_toF z)

theorem δC_δC : δC ∘ₗ δC = 0 := by
  apply LinearMap.ext
  intro z
  apply toF_injective
  rw [LinearMap.comp_apply, toF_δC, toF_δC, LinearMap.zero_apply, map_zero]
  exact LinearMap.congr_fun δF_δF (toF z)

theorem toF_chainAct (γ : principalLevel) (z : Cell →₀ ℂ) :
    toF (chainAct principalLevel γ z) = chainAct principalLevel γ (toF z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single C a => rw [chainAct_single, toF_single, toF_single, chainAct_single, Cell.smul_val]

theorem δC_equivariant : Equivariant principalLevel δC := by
  intro γ
  apply LinearMap.ext
  intro z
  apply toF_injective
  rw [LinearMap.comp_apply, LinearMap.comp_apply, toF_δC, toF_chainAct, toF_chainAct, toF_δC,
    δF_equivariant.apply]

/-- The dimension of a cell. -/
def Cell.grade (C : Cell) : ℕ := 6 - C.val.card

theorem Cell.card_le_six (C : Cell) : C.val.card ≤ 6 := by
  obtain ⟨-, v, hv⟩ := C.isCell
  rw [← v.card_M]
  exact Finset.card_le_card hv

theorem Cell.grade_le (C : Cell) : C.grade ≤ 3 := by
  have := C.isCell.1.three_le_card
  unfold Cell.grade
  omega

theorem Cell.grade_smul (γ : principalLevel) (C : Cell) : (γ • C).grade = C.grade := by
  rw [Cell.grade, Cell.grade, Cell.smul_val, card_level_smul]

theorem Cell.free (γ : principalLevel) (C : Cell) (h : γ • C = C) : γ = 1 :=
  eq_one_of_smul_eq γ C.isCell (congrArg Cell.val h)

theorem δC_grade (C D : Cell) (hD : D ∈ (δC (Finsupp.single C 1)).support) :
    D.grade + 1 = C.grade := by
  classical
  have hD' : D.val ∈ (coboundaryOf C.val).support := by
    rw [Finsupp.mem_support_iff, ← δF_single, ← toF_single, ← toF_δC, toF_apply_val]
    exact Finsupp.mem_support_iff.mp hD
  obtain ⟨w, hw, hDw⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hD')
  have hS' := Finsupp.support_smul hDw
  rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hS'
  obtain ⟨hwC, -⟩ := (mem_nbrs C.isCell.1 w).mp hw
  have hcard : D.val.card = C.val.card + 1 := by
    rw [hS', Finset.card_insert_of_notMem hwC]
  have := D.card_le_six
  unfold Cell.grade
  omega

end TernaryPeriodPolynomials.FreeResolution
