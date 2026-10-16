module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.T3Chain
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.PHLevi
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FarePeriod
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.EvalQ
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.TreeInstance

@[expose] public section


/-!
# Lemma B.1: the stabilizer sum of the standard top cell, in terms of the Hochschild-Serre quotient

`stab_sum_eq`: for the stabilizer `S = Stab_{P_H}(T₀)` (the sixteen signed monomial matrices
`diag(λ, C)`, `C` a signed permutation matrix of the last two coordinates; `stab_T0_iff`) the sum
`∑_{h ∈ S} ε(h) ρ(h) a` of `T3_chain` equals
`∑_{q ∈ S₀} det(q) ρ(q) a - ∑_{q ∈ S₀'} det(q) ρ(q) a`, where `S₀`, `S₀'` are the elements `q` of `P_H / U` with
`q • p₀ = p₀`, respectively `q • p₀ = swap p₀`, for the action on oriented Farey edges through `pibar`.  The proof
is the bijection `h ↦ h U` of `S` onto `S₀ ∪ S₀'` (`stab_inj`, `stab_exists`) together with the sign identity
`ε(h) = det(C) · (if C • p₀ = p₀ then 1 else -1)` (`sign_identity`), obtained by computing the orientation cocycle
`cellSign` on the three lines `e₀, e₁, e₂` (labels `1, 3, 9`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
open TernaryPoly.OrdinaryResidueSupport (axis)
open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry

open scoped Classical Pointwise


open TernaryPeriodPolynomials.FreeResolution TernaryPeriodPolynomials.TopVanishing
  GeneralEisenstein

section LinesA

theorem mv_PH_e0 (g : PH) : mv g.1 Cell0Geometry.e0 = ![(lamHom g : ℤ), uvec g 0, uvec g 1] := by
  funext i
  rw [mv, PH_matrix g]
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Cell0Geometry.e0, Fin.sum_univ_three]

theorem mv_PH_e1 (g : PH) : mv g.1 Cell0Geometry.e1 = ![0, (pi g).val 0 0, (pi g).val 1 0] := by
  funext i
  rw [mv, PH_matrix g]
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Cell0Geometry.e1, Fin.sum_univ_three]

theorem mv_PH_e2 (g : PH) : mv g.1 Cell0Geometry.e2 = ![0, (pi g).val 0 1, (pi g).val 1 1] := by
  funext i
  rw [mv, PH_matrix g]
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Cell0Geometry.e2, Fin.sum_univ_three]

/-- The lower-right block of an element of `P_H` is a signed permutation matrix. -/
def MonoC (C : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ((C 0 0 = 1 ∨ C 0 0 = -1) ∧ C 0 1 = 0 ∧ C 1 0 = 0 ∧ (C 1 1 = 1 ∨ C 1 1 = -1)) ∨
  (C 0 0 = 0 ∧ (C 0 1 = 1 ∨ C 0 1 = -1) ∧ (C 1 0 = 1 ∨ C 1 0 = -1) ∧ C 1 1 = 0)

theorem det_pi_cases (g : PH) : (pi g).val 0 0 * (pi g).val 1 1 - (pi g).val 0 1 * (pi g).val 1 0 = 1 ∨
    (pi g).val 0 0 * (pi g).val 1 1 - (pi g).val 0 1 * (pi g).val 1 0 = -1 := by
  have h : IsUnit (pi g).val.det := (Matrix.isUnit_iff_isUnit_det _).1 (pi g).isUnit
  rw [Matrix.det_fin_two] at h
  exact Int.isUnit_iff.mp h

theorem mk_vec_eq (x y : Vec) (h : y = x ∨ y = -x) : Line.mk x = Line.mk y :=
  Line.mk_eq_mk.mpr h

theorem vec3_eq_iff (a b c a' b' c' : ℤ) :
    (![a, b, c] : Vec) = ![a', b', c'] ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem vec3_eq_neg_iff (a b c a' b' c' : ℤ) :
    (![a, b, c] : Vec) = -![a', b', c'] ↔ a = -a' ∧ b = -b' ∧ c = -c' := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    funext i
    fin_cases i <;> rfl

theorem mem_T0set_iff (ℓ : Line) : ℓ ∈ T0set ↔
    ℓ = Line.mk Cell0Geometry.e0 ∨ ℓ = Line.mk Cell0Geometry.e1 ∨ ℓ = Line.mk Cell0Geometry.e2 := by
  simp [T0set]

theorem glGraded_T0g_iff (g : PH) : glGraded 3 g.1 T0g = T0g ↔ g.1 • T0set = T0set := by
  constructor
  · intro h
    exact congrArg (fun C : Graded 3 => C.1.val) h
  · intro h
    exact Subtype.ext (Cell.ext h)

theorem smul_T0set_iff (g : PH) : g.1 • T0set = T0set ↔ ∀ ℓ ∈ T0set, g.1 • ℓ ∈ T0set := by
  constructor
  · intro h ℓ hℓ
    rw [← h]
    exact Finset.smul_mem_smul_finset hℓ
  · intro h
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.mp hy
      exact h x hx
    · rw [card_smul_gl]

theorem stab_T0_forward (g : PH) (h : glGraded 3 g.1 T0g = T0g) :
    uvec g 0 = 0 ∧ uvec g 1 = 0 ∧ MonoC (pi g).val := by
  rw [glGraded_T0g_iff, smul_T0set_iff] at h
  have h0 := h _ (by simp [T0set] : Line.mk Cell0Geometry.e0 ∈ T0set)
  have h1 := h _ (by simp [T0set] : Line.mk Cell0Geometry.e1 ∈ T0set)
  have h2 := h _ (by simp [T0set] : Line.mk Cell0Geometry.e2 ∈ T0set)
  rw [smul_mk, mv_PH_e0, mem_T0set_iff] at h0
  rw [smul_mk, mv_PH_e1, mem_T0set_iff] at h1
  rw [smul_mk, mv_PH_e2, mem_T0set_iff] at h2
  have hl := lam_cases g
  have hd := det_pi_cases g
  simp only [Line.mk_eq_mk, Cell0Geometry.e0, Cell0Geometry.e1, Cell0Geometry.e2, vec3_eq_iff,
    vec3_eq_neg_iff] at h0 h1 h2
  refine ⟨by omega, by omega, ?_⟩
  unfold MonoC
  generalize (pi g).val 0 0 = a at *
  generalize (pi g).val 0 1 = b at *
  generalize (pi g).val 1 0 = c at *
  generalize (pi g).val 1 1 = d at *
  have hc1 : (a = 1 ∧ c = 0) ∨ (a = -1 ∧ c = 0) ∨ (a = 0 ∧ c = 1) ∨ (a = 0 ∧ c = -1) := by omega
  have hc2 : (b = 1 ∧ d = 0) ∨ (b = -1 ∧ d = 0) ∨ (b = 0 ∧ d = 1) ∨ (b = 0 ∧ d = -1) := by omega
  rcases hc1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases hc2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at hd ⊢

theorem stab_T0_backward (g : PH) (hu0 : uvec g 0 = 0) (hu1 : uvec g 1 = 0) (hC : MonoC (pi g).val) :
    glGraded 3 g.1 T0g = T0g := by
  rw [glGraded_T0g_iff, smul_T0set_iff]
  intro ℓ hℓ
  have hl := lam_cases g
  unfold MonoC at hC
  rcases (mem_T0set_iff ℓ).1 hℓ with rfl | rfl | rfl
  · rw [smul_mk, mv_PH_e0, mem_T0set_iff]
    simp only [Line.mk_eq_mk, Cell0Geometry.e0, Cell0Geometry.e1, Cell0Geometry.e2, vec3_eq_iff,
      vec3_eq_neg_iff]
    omega
  · rw [smul_mk, mv_PH_e1, mem_T0set_iff]
    simp only [Line.mk_eq_mk, Cell0Geometry.e0, Cell0Geometry.e1, Cell0Geometry.e2, vec3_eq_iff,
      vec3_eq_neg_iff, true_and, neg_zero]
    omega
  · rw [smul_mk, mv_PH_e2, mem_T0set_iff]
    simp only [Line.mk_eq_mk, Cell0Geometry.e0, Cell0Geometry.e1, Cell0Geometry.e2, vec3_eq_iff,
      vec3_eq_neg_iff, true_and, neg_zero]
    omega

theorem stab_T0_iff (g : PH) : glGraded 3 g.1 T0g = T0g ↔ uvec g 0 = 0 ∧ uvec g 1 = 0 ∧ MonoC (pi g).val :=
  ⟨stab_T0_forward g, fun h => stab_T0_backward g h.1 h.2.1 h.2.2⟩

theorem label_e0 : (Line.mk Cell0Geometry.e0).label = 1 := by
  rw [Line.label_mk]; decide +kernel

theorem label_e1 : (Line.mk Cell0Geometry.e1).label = 3 := by
  rw [Line.label_mk]; decide +kernel

theorem label_e2 : (Line.mk Cell0Geometry.e2).label = 9 := by
  rw [Line.label_mk]; decide +kernel

theorem cellSign_empty (g : IntegralGL3) : cellSign g ∅ = 1 := by
  simp [cellSign]

theorem cellSign_single (g : IntegralGL3) (c : Line) : cellSign g {c} = 1 := by
  have h := cellSign_cons g ∅ c (Finset.notMem_empty c)
  rw [Finset.insert_empty, cellSign_empty] at h
  simpa using h

theorem T0set_expand : T0set = insert (Line.mk Cell0Geometry.e0) (insert (Line.mk Cell0Geometry.e1)
    {Line.mk Cell0Geometry.e2}) := rfl

theorem e0_ne_e1 : Line.mk Cell0Geometry.e0 ≠ Line.mk Cell0Geometry.e1 := by
  intro h; have := congrArg Line.label h; rw [label_e0, label_e1] at this; omega

theorem e0_ne_e2 : Line.mk Cell0Geometry.e0 ≠ Line.mk Cell0Geometry.e2 := by
  intro h; have := congrArg Line.label h; rw [label_e0, label_e2] at this; omega

theorem e1_ne_e2 : Line.mk Cell0Geometry.e1 ≠ Line.mk Cell0Geometry.e2 := by
  intro h; have := congrArg Line.label h; rw [label_e1, label_e2] at this; omega

theorem cellSign_T0_expand (g : IntegralGL3) :
    cellSign g T0set = pairSign g (Line.mk Cell0Geometry.e1) (Line.mk Cell0Geometry.e2) *
      (pairSign g (Line.mk Cell0Geometry.e0) (Line.mk Cell0Geometry.e1) *
        pairSign g (Line.mk Cell0Geometry.e0) (Line.mk Cell0Geometry.e2)) := by
  rw [T0set_expand, cellSign_cons g _ _ (by simp [e0_ne_e1, e0_ne_e2]), cellSign_cons g _ _
    (by simpa using e1_ne_e2), cellSign_single]
  simp [Finset.prod_insert, e1_ne_e2, mul_comm, mul_assoc]

theorem pairSign_fix (g : IntegralGL3) (a b : Line) (ha : g • a = a) (hb : g • b = b) :
    pairSign g a b = 1 := by
  unfold pairSign
  rw [ha, hb]
  split_ifs
  · exact lsgn_mul_self a b
  · rfl

theorem g_smul_e0 (g : PH) (h0 : uvec g 0 = 0) (h1 : uvec g 1 = 0) :
    g.1 • Line.mk Cell0Geometry.e0 = Line.mk Cell0Geometry.e0 := by
  rw [smul_mk, mv_PH_e0]
  have hl := lam_cases g
  apply mk_vec_eq
  simp only [Cell0Geometry.e0, vec3_eq_iff, vec3_eq_neg_iff]
  omega

theorem g_smul_diag (g : PH)
    (hC : ((pi g).val 0 0 = 1 ∨ (pi g).val 0 0 = -1) ∧ (pi g).val 0 1 = 0 ∧ (pi g).val 1 0 = 0 ∧
      ((pi g).val 1 1 = 1 ∨ (pi g).val 1 1 = -1)) :
    g.1 • Line.mk Cell0Geometry.e1 = Line.mk Cell0Geometry.e1 ∧
      g.1 • Line.mk Cell0Geometry.e2 = Line.mk Cell0Geometry.e2 := by
  constructor
  · rw [smul_mk, mv_PH_e1]
    apply mk_vec_eq
    simp only [Cell0Geometry.e1, vec3_eq_iff, vec3_eq_neg_iff, true_and, neg_zero]
    omega
  · rw [smul_mk, mv_PH_e2]
    apply mk_vec_eq
    simp only [Cell0Geometry.e2, vec3_eq_iff, vec3_eq_neg_iff, true_and, neg_zero]
    omega

theorem g_smul_anti (g : PH)
    (hC : (pi g).val 0 0 = 0 ∧ ((pi g).val 0 1 = 1 ∨ (pi g).val 0 1 = -1) ∧
      ((pi g).val 1 0 = 1 ∨ (pi g).val 1 0 = -1) ∧ (pi g).val 1 1 = 0) :
    g.1 • Line.mk Cell0Geometry.e1 = Line.mk Cell0Geometry.e2 ∧
      g.1 • Line.mk Cell0Geometry.e2 = Line.mk Cell0Geometry.e1 := by
  constructor
  · rw [smul_mk, mv_PH_e1]
    apply mk_vec_eq
    simp only [Cell0Geometry.e2, vec3_eq_iff, vec3_eq_neg_iff, true_and, neg_zero]
    omega
  · rw [smul_mk, mv_PH_e2]
    apply mk_vec_eq
    simp only [Cell0Geometry.e1, vec3_eq_iff, vec3_eq_neg_iff, true_and, neg_zero]
    omega

theorem lsgn_01 : lsgn (Line.mk Cell0Geometry.e0) (Line.mk Cell0Geometry.e1) = 1 := by
  simp [lsgn, label_e0, label_e1]

theorem lsgn_02 : lsgn (Line.mk Cell0Geometry.e0) (Line.mk Cell0Geometry.e2) = 1 := by
  simp [lsgn, label_e0, label_e2]

theorem lsgn_12 : lsgn (Line.mk Cell0Geometry.e1) (Line.mk Cell0Geometry.e2) = 1 := by
  simp [lsgn, label_e1, label_e2]

theorem lsgn_21 : lsgn (Line.mk Cell0Geometry.e2) (Line.mk Cell0Geometry.e1) = -1 := by
  simp [lsgn, label_e1, label_e2]

theorem cellSign_stab (g : PH) (h : glGraded 3 g.1 T0g = T0g) :
    cellSign g.1 T0set = if (pi g).val 0 0 = 0 then -1 else 1 := by
  obtain ⟨h0, h1, hC⟩ := stab_T0_forward g h
  have hg0 := g_smul_e0 g h0 h1
  rw [cellSign_T0_expand]
  rcases hC with hC | hC
  · obtain ⟨hg1, hg2⟩ := g_smul_diag g hC
    rw [pairSign_fix _ _ _ hg0 hg1, pairSign_fix _ _ _ hg1 hg2, pairSign_fix _ _ _ hg0 hg2]
    have : (pi g).val 0 0 ≠ 0 := by rcases hC.1 with h | h <;> omega
    simp [this]
  · obtain ⟨hg1, hg2⟩ := g_smul_anti g hC
    have e1 : pairSign g.1 (Line.mk Cell0Geometry.e1) (Line.mk Cell0Geometry.e2) = -1 := by
      unfold pairSign
      rw [hg1, hg2, ite_eq_left (by simp [label_e1, label_e2]), lsgn_12, lsgn_21]
      norm_num
    have e2 : pairSign g.1 (Line.mk Cell0Geometry.e0) (Line.mk Cell0Geometry.e1) = 1 := by
      unfold pairSign
      rw [hg0, hg1, ite_eq_left (by simp [label_e0, label_e1, label_e2]), lsgn_01, lsgn_02]
      norm_num
    have e3 : pairSign g.1 (Line.mk Cell0Geometry.e0) (Line.mk Cell0Geometry.e2) = 1 := by
      unfold pairSign
      rw [hg0, hg2, ite_eq_left (by simp [label_e0, label_e1, label_e2]), lsgn_02, lsgn_01]
      norm_num
    rw [e1, e2, e3, ite_eq_left hC.1]
    norm_num

end LinesA

section QSide

open TernaryPeriodPolynomials.Argument.FareyTree

theorem fixed_iff (C : GL2Z) : C • p0 = p0 ↔
    ((C.val 0 0 = 1 ∧ C.val 0 1 = 0 ∧ C.val 1 0 = 0 ∧ C.val 1 1 = 1) ∨
    (C.val 0 0 = -1 ∧ C.val 0 1 = 0 ∧ C.val 1 0 = 0 ∧ C.val 1 1 = -1) ∨
    (C.val 0 0 = 0 ∧ C.val 0 1 = 1 ∧ C.val 1 0 = 1 ∧ C.val 1 1 = 0) ∨
    (C.val 0 0 = 0 ∧ C.val 0 1 = -1 ∧ C.val 1 0 = -1 ∧ C.val 1 1 = 0)) :=
  ⟨fun h => stab_p0_entries C h, fun h => stab_p0_of_entries C h⟩

theorem sOne_val00 : sOne.val 0 0 = 1 := by simp [sOne, colGL_val_zero, FareyTree.e1]
theorem sOne_val10 : sOne.val 1 0 = 0 := by simp [sOne, colGL_val_zero, FareyTree.e1]
theorem sOne_val01 : sOne.val 0 1 = 0 := by simp [sOne, colGL_val_one, FareyTree.e2]
theorem sOne_val11 : sOne.val 1 1 = -1 := by simp [sOne, colGL_val_one, FareyTree.e2]

theorem swap_iff (C : GL2Z) : C • p0 = p0.swap ↔
    ((C.val 0 0 = 1 ∧ C.val 0 1 = 0 ∧ C.val 1 0 = 0 ∧ C.val 1 1 = -1) ∨
    (C.val 0 0 = -1 ∧ C.val 0 1 = 0 ∧ C.val 1 0 = 0 ∧ C.val 1 1 = 1) ∨
    (C.val 0 0 = 0 ∧ C.val 0 1 = 1 ∧ C.val 1 0 = -1 ∧ C.val 1 1 = 0) ∨
    (C.val 0 0 = 0 ∧ C.val 0 1 = -1 ∧ C.val 1 0 = 1 ∧ C.val 1 1 = 0)) := by
  have h1 : C • p0 = p0.swap ↔ (sOne * C) • p0 = p0 := by
    constructor
    · intro h
      rw [mul_smul, h, ← sOne_smul_p0, ← mul_smul, sOne_mul_self, one_smul]
    · intro h
      rw [mul_smul] at h
      have h2 := congrArg (fun x => sOne • x) h
      rw [smul_smul, sOne_mul_self, one_smul, sOne_smul_p0] at h2
      exact h2
  rw [h1]
  have hs : ∀ i j, (sOne * C).val i j = (sOne.val i 0 * C.val 0 j + sOne.val i 1 * C.val 1 j) := by
    intro i j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [fixed_iff]
  simp only [hs, sOne_val00, sOne_val10, sOne_val01, sOne_val11]
  generalize C.val 0 0 = a
  generalize C.val 0 1 = b
  generalize C.val 1 0 = c
  generalize C.val 1 1 = d
  omega

theorem sign_identity (g : PH) (h : glGraded 3 g.1 T0g = T0g) :
    cellSign g.1 T0set = (((pi g).val.det : ℤ) : ℚ) * (if (pi g) • p0 = p0 then 1 else -1) := by
  obtain ⟨-, -, hC⟩ := stab_T0_forward g h
  rw [cellSign_stab g h, fixed_iff, Matrix.det_fin_two]
  unfold MonoC at hC
  generalize (pi g).val 0 0 = a at *
  generalize (pi g).val 0 1 = b at *
  generalize (pi g).val 1 0 = c at *
  generalize (pi g).val 1 1 = d at *
  rcases hC with ⟨ha | ha, hb, hc, hd | hd⟩ | ⟨ha, hb | hb, hc | hc, hd⟩ <;> subst_vars <;> norm_num

theorem monoC_of_fixed_or_swap (C : GL2Z) (h : C • p0 = p0 ∨ C • p0 = p0.swap) : MonoC C.val := by
  rw [fixed_iff, swap_iff] at h
  unfold MonoC
  generalize C.val 0 0 = a at *
  generalize C.val 0 1 = b at *
  generalize C.val 1 0 = c at *
  generalize C.val 1 1 = d at *
  omega

theorem fixed_or_swap_of_monoC (C : GL2Z) (h : MonoC C.val) : C • p0 = p0 ∨ C • p0 = p0.swap := by
  rw [fixed_iff, swap_iff]
  unfold MonoC at h
  generalize C.val 0 0 = a at *
  generalize C.val 0 1 = b at *
  generalize C.val 1 0 = c at *
  generalize C.val 1 1 = d at *
  rcases h with ⟨ha | ha, hb, hc, hd | hd⟩ | ⟨ha, hb | hb, hc | hc, hd⟩ <;> subst_vars <;> norm_num

theorem p0_ne_swap : p0 ≠ p0.swap := by
  intro h
  have h2 : sOne • p0 = p0 := by rw [sOne_smul_p0]; exact h.symm
  have := stab_p0_entries sOne h2
  rw [sOne_val00, sOne_val01, sOne_val10, sOne_val11] at this
  omega

end QSide

section Bij

theorem stab_inj (h h' : PH) (hs : glGraded 3 h.1 T0g = T0g) (hs' : glGraded 3 h'.1 T0g = T0g)
    (e : (QuotientGroup.mk h : PH ⧸ U) = QuotientGroup.mk h') : h = h' := by
  obtain ⟨hu0, hu1, -⟩ := stab_T0_forward h hs
  obtain ⟨hu0', hu1', -⟩ := stab_T0_forward h' hs'
  have hmem : h⁻¹ * h' ∈ U := QuotientGroup.eq.mp e
  obtain ⟨hp, hl⟩ := mem_U.mp hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at hp hl
  apply PH_ext hl hp
  funext i
  fin_cases i
  · exact hu0.trans hu0'.symm
  · exact hu1.trans hu1'.symm

theorem stab_exists (g : PH) (hm : MonoC (pi g).val) :
    ∃ h : PH, glGraded 3 h.1 T0g = T0g ∧ (QuotientGroup.mk h : PH ⧸ U) = QuotientGroup.mk g := by
  let w : Multiplicative (Fin 2 → ℤ) := Multiplicative.ofAdd (fun i => -((lamHom g : ℤ) * uvec g i))
  have hr : radPH w ∈ U := radPH_mem_U w
  have hl := lam_cases g
  refine ⟨radPH w * g, ?_, ?_⟩
  · have hu : ∀ i, uvec (radPH w * g) i = 0 := by
      intro i
      have h1 : uvec (radPH w * g) i = Multiplicative.toAdd w i * g.1.val 0 0 + uvec g i := by
        fin_cases i <;> simp [uvec, radPH_val, Matrix.mul_apply, Fin.sum_univ_three, w]
      rw [h1]
      have h2 : g.1.val 0 0 = (lamHom g : ℤ) := rfl
      rw [h2]
      simp only [w, toAdd_ofAdd]
      rcases hl with h | h <;> rw [h] <;> ring
    refine stab_T0_backward _ (hu 0) (hu 1) ?_
    rw [map_mul, pi_radPH, one_mul]
    exact hm
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (radPH w)).mpr hr, one_mul]

end Bij

instance FibRep_isTrivial (n : ℕ) : Representation.IsTrivial ((FibRep n).ρ.comp U.subtype) :=
  ⟨fun u => FibRep_U n u⟩

open TernaryPeriodPolynomials.Argument.FareyTree in
theorem stab_sum_eq (n : ℕ) (a : ResidueFiber n (axis 0)) (S : Finset PH)
    (hS : ∀ h, h ∈ S ↔ glGraded 3 h.1 T0g = T0g) (S₀ S₀' : Finset (PH ⧸ U))
    (hS₀ : ∀ q, q ∈ S₀ ↔ (letI := HochschildSerre.oteMulActionQ pibar; q • p0 = p0))
    (hS₀' : ∀ q, q ∈ S₀' ↔ (letI := HochschildSerre.oteMulActionQ pibar; q • p0 = p0.swap)) :
    ∑ h ∈ S, stabTerm n a h =
      (∑ q ∈ S₀, (((pibar q).val.det : ℤ) : ℚ) • (HochschildSerre.Abar U (FibRep n)).ρ q a) -
        ∑ q ∈ S₀', (((pibar q).val.det : ℤ) : ℚ) • (HochschildSerre.Abar U (FibRep n)).ρ q a := by
  let f : PH ⧸ U → ResidueFiber n (axis 0) := fun q =>
    (((pibar q).val.det : ℤ) : ℚ) • (HochschildSerre.Abar U (FibRep n)).ρ q a
  have hdis : Disjoint S₀ S₀' := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    rw [hS₀] at h1
    rw [hS₀'] at h2
    exact p0_ne_swap (h1.symm.trans h2)
  have key : ∑ h ∈ S, stabTerm n a h = ∑ q ∈ S₀ ∪ S₀', (if q ∈ S₀ then f q else -f q) := by
    refine Finset.sum_bij (fun h _ => (QuotientGroup.mk h : PH ⧸ U)) ?_ ?_ ?_ ?_
    · intro h hh
      obtain ⟨-, -, hm⟩ := stab_T0_forward h ((hS h).mp hh)
      rcases fixed_or_swap_of_monoC (pi h) hm with h1 | h1
      · exact Finset.mem_union_left _ ((hS₀ _).mpr h1)
      · exact Finset.mem_union_right _ ((hS₀' _).mpr h1)
    · intro h1 hh1 h2 hh2 e
      exact stab_inj h1 h2 ((hS h1).mp hh1) ((hS h2).mp hh2) e
    · intro q hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hm : MonoC (pi g).val := by
        apply monoC_of_fixed_or_swap
        rcases Finset.mem_union.mp hq with h1 | h1
        · exact Or.inl (show (pi g) • p0 = p0 from (hS₀ (QuotientGroup.mk g)).mp h1)
        · exact Or.inr (show (pi g) • p0 = p0.swap from (hS₀' (QuotientGroup.mk g)).mp h1)
      obtain ⟨h, hh, e⟩ := stab_exists g hm
      exact ⟨h, (hS h).mpr hh, e⟩
    · intro h hh
      have hsg := sign_identity h ((hS h).mp hh)
      have hmem : (QuotientGroup.mk h : PH ⧸ U) ∈ S₀ ↔ (pi h) • p0 = p0 := hS₀ _
      unfold stabTerm
      change cellSign h.1 T0set • fiberAction n h.1 a = _
      rw [hsg]
      by_cases hfx : (pi h) • p0 = p0
      · rw [ite_eq_left (hmem.mpr hfx), ite_eq_left hfx, mul_one]
        rfl
      · rw [ite_eq_right (fun h' => hfx (hmem.mp h')), ite_eq_right hfx, mul_neg_one, neg_smul]
        rfl
  rw [key, Finset.sum_union hdis]
  have e2 : ∑ q ∈ S₀', (if q ∈ S₀ then f q else -f q) = -∑ q ∈ S₀', f q := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [ite_eq_right (fun h' => Finset.disjoint_left.mp hdis h' hq)]
  rw [e2, sub_eq_add_neg]
  congr 1
  exact Finset.sum_congr rfl fun q hq => ite_eq_left hq

end TernaryPeriodPolynomials.Argument.AppendixBResidue
