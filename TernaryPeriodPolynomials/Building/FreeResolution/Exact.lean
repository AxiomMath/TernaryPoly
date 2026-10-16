module

public import TernaryPeriodPolynomials.Building.FreeResolution.Complex
public import TernaryPeriodPolynomials.Building.FreeResolution.Orientation
public import TernaryPeriodPolynomials.Building.FreeResolution.Morse

@[expose] public section


/-!
# Acyclicity of the well-rounded complex

Original work by Claude Opus 5.5.

The augmentation sends a vertex (a cell with six lines) to its orientation `ι(ε v)`; it kills
boundaries of edges because the two vertices of an edge have cancelling orientations. Exactness is
the discrete Morse argument (`morse_exact`) for the owner filtration: the cells owned by a vertex
`v` are exactly the sets between the ascending lines `up v` and `M v`, a boolean interval on which
removing a fixed descending line `j₀` is a contracting homotopy; a vertex without descending lines
is the minimum and owns only itself.
-/

noncomputable section

namespace TernaryPeriodPolynomials.FreeResolution

open GeneralEisenstein Matrix TernaryPeriodPolynomials.TopVanishing
open scoped Pointwise

/-! ### Owners of cells -/

theorem isCell_of_up_subset {v : Vtx} {T : Finset Line} (hup : v.up ⊆ T) (hT : T ⊆ v.M) :
    IsCell T :=
  ⟨v.up_spans.mono hup, v, hT⟩

/-- The owner of an enlarged cell. -/
theorem owner_insert_of_mem {T : Finset Line} (hT : IsCell T) {v : Vtx} (hv : owner T = v)
    {w : Line} (hw : w ∈ v.M) : owner (insert w T) = v := by
  obtain ⟨hsub, -⟩ := owner_spec hT.1 hT.2
  rw [hv] at hsub
  have hins : insert w T ⊆ v.M := Finset.insert_subset hw hsub
  refine (owner_eq_iff (hT.1.mono (Finset.subset_insert _ _)) hins).mpr fun ℓ hℓ hℓT => ?_
  have h1 := (owner_eq_iff hT.1 hsub).mp hv
  exact h1 ℓ hℓ fun h => hℓT (Finset.mem_insert_of_mem h)

theorem owner_insert_le {T : Finset Line} (hT : IsCell T) {w : Line} (hw : w ∈ nbrs T) :
    owner (insert w T) ≤ owner T := by
  obtain ⟨-, hs⟩ := (mem_nbrs hT.1 w).mp hw
  have hS : Spans (insert w T) := hT.1.mono (Finset.subset_insert _ _)
  obtain ⟨h1, -⟩ := owner_spec hS hs
  exact (owner_spec hT.1 hT.2).2 _ ((Finset.subset_insert _ _).trans h1)

theorem mem_support_coboundaryOf {T S : Finset Line} (hS : S ∈ (coboundaryOf T).support) :
    ∃ w ∈ nbrs T, S = insert w T := by
  classical
  obtain ⟨w, hw, hSw⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hS)
  have hS' := Finsupp.support_smul hSw
  rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hS'
  exact ⟨w, hw, hS'⟩

theorem owner_le_of_support (C D : Cell) (hD : D ∈ (δC (Finsupp.single C 1)).support) :
    owner D.val ≤ owner C.val := by
  have hD' : D.val ∈ (coboundaryOf C.val).support := by
    rw [Finsupp.mem_support_iff, ← δF_single, ← toF_single, ← toF_δC, toF_apply_val]
    exact Finsupp.mem_support_iff.mp hD
  obtain ⟨w, hw, hDw⟩ := mem_support_coboundaryOf hD'
  rw [hDw]
  exact owner_insert_le C.isCell hw

/-! ### The augmentation -/

/-- The orientation of a vertex cell (zero for cells of positive dimension). -/
def epsF (T : Finset Line) : ℂ := if T.card = 6 then iota (epsMod T) else 0

/-- The augmentation on chains of sets of lines. -/
def εF : (Finset Line →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ epsF

/-- The augmentation of the well-rounded complex. -/
def εC : (Cell →₀ ℂ) →ₗ[ℂ] ℂ := εF ∘ₗ toF

theorem εC_single_smul (C : Cell) (a : ℂ) : εC (Finsupp.single C a) = a * epsF C.val := by
  rw [εC, LinearMap.comp_apply, toF_single, εF, Finsupp.linearCombination_single, smul_eq_mul]

theorem εC_single (C : Cell) : εC (Finsupp.single C 1) = epsF C.val := by
  rw [εC_single_smul, one_mul]

theorem epsMod_smul (γ : principalLevel) (T : Finset Line) : epsMod (γ • T) = epsMod T := by
  rw [epsMod, epsMod, image_label_smul]

theorem epsF_smul (γ : principalLevel) (T : Finset Line) : epsF (γ • T) = epsF T := by
  rw [epsF, epsF, card_level_smul, epsMod_smul]

theorem εC_invariant (γ : principalLevel) (z : Cell →₀ ℂ) :
    εC (chainAct principalLevel γ z) = εC z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single C a =>
    rw [chainAct_single, εC_single_smul, εC_single_smul, Cell.smul_val, epsF_smul]

theorem εC_grade (C : Cell) (h : C.grade ≠ 0) : εC (Finsupp.single C 1) = 0 := by
  rw [εC_single, epsF, ite_eq_right]
  intro h6
  apply h
  rw [Cell.grade, h6]

/-- A five-element cell is a facet `M v ∖ {ℓ}` of a vertex. -/
theorem exists_facet {T : Finset Line} (hT : IsCell T) (h5 : T.card = 5) :
    ∃ v : Vtx, ∃ ℓ ∈ v.M, T = v.M.erase ℓ := by
  obtain ⟨-, v, hv⟩ := hT
  have hlt : T.card < v.M.card := by rw [h5, v.card_M]; norm_num
  obtain ⟨ℓ, hℓ, hℓT⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨v, ℓ, hℓ, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro t ht
    exact Finset.mem_erase.mpr ⟨fun h => hℓT (by rw [← h]; exact ht), hv ht⟩
  · rw [Finset.card_erase_of_mem hℓ, v.card_M, h5]

theorem εF_coboundaryOf_eq (T : Finset Line) :
    εF (coboundaryOf T) = ∑ w ∈ nbrs T, insSign T w * epsF (insert w T) := by
  unfold coboundaryOf
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, εF, Finsupp.linearCombination_single, one_smul, smul_eq_mul]

theorem epsF_vertex (u : Vtx) : epsF u.M = iota (epsMod u.M) := by
  rw [epsF, ite_eq_left u.card_M]

/-- The neighbours of a facet are the two lines completing it to a vertex. -/
theorem nbrs_facet (v : Vtx) {ℓ ℓ' : Line} (hℓ : ℓ ∈ v.M) (hT : Spans (v.M.erase ℓ))
    (hn2 : ℓ' ∉ v.M) (hnb : (v.nb ℓ).M = insert ℓ' (v.M.erase ℓ)) :
    nbrs (v.M.erase ℓ) = {ℓ, ℓ'} := by
  ext w
  rw [mem_nbrs hT, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hwT, B, hB⟩
    have hBsub : v.M.erase ℓ ⊆ B.M := (Finset.subset_insert _ _).trans hB
    have hwB : w ∈ B.M := hB (Finset.mem_insert_self _ _)
    rcases v.eq_or_eq_nb_of_facet hℓ B hBsub with hB' | hB'
    · left
      rw [hB'] at hwB
      by_contra hwl
      exact hwT (Finset.mem_erase.mpr ⟨hwl, hwB⟩)
    · right
      rw [hB', hnb] at hwB
      rcases Finset.mem_insert.mp hwB with h | h
      · exact h
      · exact absurd h hwT
  · rintro (h | h)
    · rw [h]
      exact ⟨Finset.notMem_erase _ _, v, fun x hx => by rwa [Finset.insert_erase hℓ] at hx⟩
    · rw [h]
      exact ⟨fun h' => hn2 (Finset.mem_of_mem_erase h'), v.nb ℓ,
        fun x hx => by rwa [← hnb] at hx⟩

/-- The two vertices of an edge contribute opposite orientations. -/
theorem facet_sum (v : Vtx) {ℓ ℓ' : Line} (hℓ : ℓ ∈ v.M) (hn1 : ℓ' ∈ (v.nb ℓ).M)
    (hn2 : ℓ' ∉ v.M) (hnb : (v.nb ℓ).M = insert ℓ' (v.M.erase ℓ)) :
    insSign (v.M.erase ℓ) ℓ * epsF (insert ℓ (v.M.erase ℓ)) +
      insSign (v.M.erase ℓ) ℓ' * epsF (insert ℓ' (v.M.erase ℓ)) = 0 := by
  have h1 : epsF (insert ℓ (v.M.erase ℓ)) = iota (epsMod v.M) := by
    rw [Finset.insert_erase hℓ]
    exact epsF_vertex v
  have h2 : epsF (insert ℓ' (v.M.erase ℓ)) = iota (epsMod (v.nb ℓ).M) := by
    rw [← hnb]
    exact epsF_vertex _
  rw [h1, h2]
  linear_combination edge_sign v hℓ hn1 hn2

theorem εF_coboundaryOf_facet (v : Vtx) {ℓ ℓ' : Line} (hℓ : ℓ ∈ v.M)
    (hT : Spans (v.M.erase ℓ)) (hn1 : ℓ' ∈ (v.nb ℓ).M) (hn2 : ℓ' ∉ v.M) :
    εF (coboundaryOf (v.M.erase ℓ)) = 0 := by
  have hnb := nb_M_eq v hℓ hn1 hn2
  have hne : ℓ ≠ ℓ' := fun h => hn2 (by rw [← h]; exact hℓ)
  rw [εF_coboundaryOf_eq, nbrs_facet v hℓ hT hn2 hnb, Finset.sum_pair hne]
  exact facet_sum v hℓ hn1 hn2 hnb

theorem εF_coboundaryOf_of_card_ne {T : Finset Line} (hT : Spans T) (h5 : T.card ≠ 5) :
    εF (coboundaryOf T) = 0 := by
  rw [εF_coboundaryOf_eq]
  refine Finset.sum_eq_zero fun w hw => ?_
  obtain ⟨hwT, -⟩ := (mem_nbrs hT w).mp hw
  have h6 : (insert w T).card ≠ 6 := by
    rw [Finset.card_insert_of_notMem hwT]
    omega
  rw [epsF, ite_eq_right h6, mul_zero]

theorem εF_coboundaryOf {T : Finset Line} (hT : IsCell T) : εF (coboundaryOf T) = 0 := by
  by_cases h5 : T.card = 5
  · obtain ⟨v, ℓ, hℓ, rfl⟩ := exists_facet hT h5
    obtain ⟨i, hi⟩ := v.exists_index hℓ
    have hn1 : v.frame⁻¹ • Line.mk (mNew i) ∈ (v.nb ℓ).M := by
      rw [hi]
      exact v.mem_nb i
    exact εF_coboundaryOf_facet v hℓ hT.1 hn1 (v.new_not_mem i)
  · exact εF_coboundaryOf_of_card_ne hT.1 h5

theorem εC_δC : εC ∘ₗ δC = 0 := by
  apply Finsupp.lhom_ext
  intro C a
  have e : Finsupp.single C a = a • Finsupp.single C (1 : ℂ) := by simp
  rw [LinearMap.comp_apply, LinearMap.zero_apply, e, map_smul, map_smul, εC,
    LinearMap.comp_apply, toF_δC, toF_single, δF_single, εF_coboundaryOf C.isCell, smul_zero]

/-! ### The Morse homotopy on the cells owned by a vertex -/

theorem filter_single_eq {α : Type} (p : α → Prop) [DecidablePred p] (a : α) (b : ℂ) :
    (Finsupp.single a b).filter p = if p a then Finsupp.single a b else 0 := by
  classical
  ext x
  rw [Finsupp.filter_apply]
  by_cases hx : a = x
  · subst hx
    by_cases hp : p a
    · rw [ite_eq_left hp, ite_eq_left hp]
    · rw [ite_eq_right hp, ite_eq_right hp, Finsupp.zero_apply]
  · have h0 : Finsupp.single a b x = 0 := by rw [Finsupp.single_apply, ite_eq_right hx]
    rw [h0]
    split_ifs <;> simp [h0]

section Homotopy

variable (v : Vtx) (j0 : Line)

open Classical in
/-- Removing the descending line `j₀` from a cell owned by `v`. -/
def hF (T : Finset Line) : Finset Line →₀ ℂ :=
  if owner T = v ∧ j0 ∈ T ∧ IsCell T then insSign (T.erase j0) j0 • Finsupp.single (T.erase j0) 1
  else 0

/-- The owned part of a chain on sets of lines. -/
abbrev PF : (Finset Line →₀ ℂ) →ₗ[ℂ] (Finset Line →₀ ℂ) := ownedPart owner v

variable {v j0}

theorem PF_δF_single {S : Finset Line} (hS : IsCell S) (hSv : owner S = v) :
    PF v (δF (Finsupp.single S 1)) =
      ∑ w ∈ v.M \ S, insSign S w • Finsupp.single (insert w S) 1 := by
  rw [δF_single, coboundaryOf, map_sum]
  have hfilter : (nbrs S).filter (fun w => owner (insert w S) = v) = v.M \ S := by
    ext w
    rw [Finset.mem_filter, mem_nbrs hS.1, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hwS, hs⟩, hown⟩
      have hS' : Spans (insert w S) := hS.1.mono (Finset.subset_insert _ _)
      have := (owner_spec hS' hs).1
      rw [hown] at this
      exact ⟨this (Finset.mem_insert_self _ _), hwS⟩
    · rintro ⟨hwM, hwS⟩
      obtain ⟨hsub, -⟩ := owner_spec hS.1 hS.2
      rw [hSv] at hsub
      exact ⟨⟨hwS, v, Finset.insert_subset hwM hsub⟩, owner_insert_of_mem hS hSv hwM⟩
  rw [← hfilter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul]
  show insSign S w • (Finsupp.single (insert w S) (1 : ℂ)).filter (fun T => owner T = v) = _
  rw [filter_single_eq]
  split_ifs <;> simp

theorem hF_ne (T : Finset Line) (hT : IsCell T) (hTv : owner T = v) (hj : j0 ∈ T) :
    hF v j0 T = insSign (T.erase j0) j0 • Finsupp.single (T.erase j0) 1 := by
  rw [hF, ite_eq_left ⟨hTv, hj, hT⟩]

theorem hF_eq_zero (T : Finset Line) (hj : j0 ∉ T) : hF v j0 T = 0 := by
  rw [hF, ite_eq_right (fun h => hj h.2.1)]

theorem up_subset_erase (hdesc : v.nb j0 < v) {T : Finset Line} (hT : IsCell T)
    (hTv : owner T = v) :
    v.up ⊆ T.erase j0 := by
  intro ℓ hℓ
  have h1 := Vtx.up_subset_of_owner hT.1 hT.2
  rw [hTv] at h1
  refine Finset.mem_erase.mpr ⟨fun h => ?_, h1 hℓ⟩
  rw [h] at hℓ
  exact (Finset.mem_filter.mp hℓ).2 hdesc

theorem isCell_erase (hdesc : v.nb j0 < v) {T : Finset Line} (hT : IsCell T)
    (hTv : owner T = v) : IsCell (T.erase j0) := by
  obtain ⟨hsub, -⟩ := owner_spec hT.1 hT.2
  rw [hTv] at hsub
  exact isCell_of_up_subset (up_subset_erase hdesc hT hTv)
    ((Finset.erase_subset _ _).trans hsub)

theorem owner_erase (hdesc : v.nb j0 < v) {T : Finset Line} (hT : IsCell T)
    (hTv : owner T = v) : owner (T.erase j0) = v := by
  obtain ⟨hsub, -⟩ := owner_spec hT.1 hT.2
  rw [hTv] at hsub
  have hc := isCell_erase hdesc hT hTv
  refine (owner_eq_iff hc.1 ((Finset.erase_subset _ _).trans hsub)).mpr fun ℓ hℓ hℓT => ?_
  by_cases h : ℓ = j0
  · rw [h]
    exact hdesc
  · exact (owner_eq_iff hT.1 hsub).mp hTv ℓ hℓ fun h' => hℓT (Finset.mem_erase.mpr ⟨h, h'⟩)

/-- The homotopy identity on the cells owned by `v`. -/
theorem homotopy_identity (hj0 : j0 ∈ v.M) (hdesc : v.nb j0 < v) {T : Finset Line}
    (hT : IsCell T) (hTv : owner T = v) :
    PF v (δF (hF v j0 T)) + Finsupp.linearCombination ℂ (hF v j0) (PF v (δF (Finsupp.single T 1)))
      = Finsupp.single T 1 := by
  obtain ⟨hsub, -⟩ := owner_spec hT.1 hT.2
  rw [hTv] at hsub
  have hlin : ∀ w ∈ v.M \ T, hF v j0 (insert w T) =
      if j0 ∈ insert w T then insSign ((insert w T).erase j0) j0 •
        Finsupp.single ((insert w T).erase j0) 1 else 0 := by
    intro w hw
    obtain ⟨hwM, hwT⟩ := Finset.mem_sdiff.mp hw
    have hc : IsCell (insert w T) :=
      ⟨hT.1.mono (Finset.subset_insert _ _), v, Finset.insert_subset hwM hsub⟩
    rw [hF]
    by_cases hj : j0 ∈ insert w T
    · rw [ite_eq_left ⟨owner_insert_of_mem hT hTv hwM, hj, hc⟩, ite_eq_left hj]
    · rw [ite_eq_right (fun h => hj h.2.1), ite_eq_right hj]
  rw [PF_δF_single hT hTv, map_sum]
  simp only [map_smul, Finsupp.linearCombination_single, one_smul]
  by_cases hjT : j0 ∈ T
  · -- the line `j₀` lies in the cell
    have hc' := isCell_erase hdesc hT hTv
    have ho' := owner_erase hdesc hT hTv
    rw [hF_ne T hT hTv hjT, map_smul, map_smul, PF_δF_single hc' ho']
    have hsd : v.M \ T.erase j0 = insert j0 (v.M \ T) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hxM, hx⟩
        by_cases hxj : x = j0
        · exact Or.inl hxj
        · exact Or.inr ⟨hxM, fun h => hx ⟨hxj, h⟩⟩
      · rintro (rfl | ⟨hxM, hxT⟩)
        · exact ⟨hj0, fun h => h.1 rfl⟩
        · exact ⟨hxM, fun h => hxT h.2⟩
    have hj0n : j0 ∉ v.M \ T := fun h => (Finset.mem_sdiff.mp h).2 hjT
    rw [hsd, Finset.sum_insert hj0n, Finset.insert_erase hjT, smul_add, smul_smul,
      insSign_sq, one_smul, add_assoc, Finset.smul_sum, ← Finset.sum_add_distrib]
    conv_rhs => rw [← add_zero (Finsupp.single T (1 : ℂ))]
    congr 1
    refine Finset.sum_eq_zero fun w hw => ?_
    obtain ⟨hwM, hwT⟩ := Finset.mem_sdiff.mp hw
    have hwj : w ≠ j0 := fun h => hwT (by rw [h]; exact hjT)
    rw [hlin w hw, ite_eq_left (Finset.mem_insert_of_mem hjT), Finset.erase_insert_of_ne hwj, smul_smul,
      smul_smul, ← add_smul]
    -- the two insertion orders cancel
    have hS : IsSimplex (insert w T) := ⟨v, Finset.insert_subset hwM hsub⟩
    have hjT' : j0 ∉ T.erase j0 := Finset.notMem_erase _ _
    have hwT' : w ∉ T.erase j0 := fun h => hwT (Finset.mem_of_mem_erase h)
    have hS1 : IsSimplex (insert j0 (T.erase j0)) := by
      rw [Finset.insert_erase hjT]
      exact ⟨v, hsub⟩
    have hS2 : IsSimplex (insert w (T.erase j0)) :=
      hS.mono (Finset.insert_subset_insert _ (Finset.erase_subset _ _))
    have hl1 := label_not_mem_of_simplex hS1 hjT'
    have hl2 := label_not_mem_of_simplex hS2 hwT'
    have hl12 : j0.label ≠ w.label := by
      intro h
      apply hwj
      exact (hS.label_injOn (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hjT)) h.symm)
    have hswap := insSign_swap (T.erase j0) hl1 hl2 hl12
    rw [Finset.insert_erase hjT] at hswap
    have ha := insSign_sq (T.erase j0) j0
    have hd := insSign_sq (insert w (T.erase j0)) j0
    have : insSign (T.erase j0) j0 * insSign (T.erase j0) w +
        insSign T w * insSign (insert w (T.erase j0)) j0 = 0 := by
      linear_combination (insSign (T.erase j0) j0 * insSign (insert w (T.erase j0)) j0) * hswap
        - (insSign T w * insSign (insert w (T.erase j0)) j0) * ha
        - (insSign (T.erase j0) j0 * insSign (T.erase j0) w) * hd
    rw [this, zero_smul]
  · -- the line `j₀` is not in the cell
    rw [hF_eq_zero T hjT, map_zero, map_zero, zero_add]
    have hj0m : j0 ∈ v.M \ T := Finset.mem_sdiff.mpr ⟨hj0, hjT⟩
    rw [Finset.sum_eq_single j0]
    · rw [hlin j0 hj0m, ite_eq_left (Finset.mem_insert_self _ _), Finset.erase_insert hjT, smul_smul,
        insSign_sq, one_smul]
    · intro w hw hwj
      rw [hlin w hw, ite_eq_right, smul_zero]
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hwj h.symm
      · exact hjT h
    · intro h
      exact absurd hj0m h

end Homotopy

/-! ### Transport to cells -/

theorem toF_ownedPart (v : Vtx) (z : Cell →₀ ℂ) :
    toF (ownedPart (fun C : Cell => owner C.val) v z) = ownedPart owner v (toF z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single C a =>
    show toF ((Finsupp.single C a).filter fun D => owner D.val = v) =
      (toF (Finsupp.single C a)).filter fun T => owner T = v
    rw [toF_single, filter_single_eq, filter_single_eq]
    split_ifs <;> simp [toF_single]

section CellHomotopy

variable {v : Vtx} {j0 : Line}

theorem cellSupp_hF (hdesc : v.nb j0 < v) (T : Finset Line) : CellSupp (hF v j0 T) := by
  intro S hS
  rw [hF] at hS
  split_ifs at hS with h
  · have hS' := Finsupp.support_smul hS
    rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hS'
    rw [hS']
    exact isCell_erase hdesc h.2.2 h.1
  · simp at hS

theorem toF_ofF_hF (hdesc : v.nb j0 < v) (T : Finset Line) :
    toF (ofF (hF v j0 T)) = hF v j0 T :=
  toF_ofF (cellSupp_hF hdesc T)

theorem toF_linearCombination_hF (hdesc : v.nb j0 < v) (z : Cell →₀ ℂ) :
    toF (Finsupp.linearCombination ℂ (fun C : Cell => ofF (hF v j0 C.val)) z) =
      Finsupp.linearCombination ℂ (hF v j0) (toF z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single C a =>
    rw [Finsupp.linearCombination_single, map_smul, toF_ofF_hF hdesc, toF_single,
      Finsupp.linearCombination_single]

theorem cell_homotopy_identity (hj0 : j0 ∈ v.M) (hdesc : v.nb j0 < v) (C : Cell)
    (hC : owner C.val = v) :
    (δC (ofF (hF v j0 C.val))).filter (fun D => owner D.val = v) +
      Finsupp.linearCombination ℂ (fun C : Cell => ofF (hF v j0 C.val))
        ((δC (Finsupp.single C 1)).filter (fun D => owner D.val = v)) =
      Finsupp.single C 1 := by
  apply toF_injective
  have e1 : (δC (ofF (hF v j0 C.val))).filter (fun D => owner D.val = v) =
      ownedPart (fun D : Cell => owner D.val) v (δC (ofF (hF v j0 C.val))) := rfl
  have e2 : (δC (Finsupp.single C 1)).filter (fun D => owner D.val = v) =
      ownedPart (fun D : Cell => owner D.val) v (δC (Finsupp.single C 1)) := rfl
  rw [e1, e2, map_add, toF_ownedPart, toF_linearCombination_hF hdesc, toF_ownedPart, toF_δC,
    toF_δC, toF_ofF_hF hdesc, toF_single]
  exact homotopy_identity hj0 hdesc C.isCell hC

theorem owner_support_hF (hdesc : v.nb j0 < v) (C : Cell) (hC : owner C.val = v) (D : Cell)
    (hD : D ∈ (ofF (hF v j0 C.val)).support) : owner D.val = v := by
  have hD' : D.val ∈ (hF v j0 C.val).support := by
    rw [Finsupp.mem_support_iff, ← toF_apply_val, toF_ofF_hF hdesc] at hD
    exact Finsupp.mem_support_iff.mpr hD
  rw [hF] at hD'
  split_ifs at hD' with h
  · have hS' := Finsupp.support_smul hD'
    rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hS'
    rw [hS']
    exact owner_erase hdesc C.isCell hC
  · simp at hD'

end CellHomotopy

/-- The cell of a vertex. -/
def Vtx.cell (v : Vtx) : Cell :=
  ⟨v.M, v.up_spans.mono (Finset.filter_subset _ _), v, subset_refl _⟩

theorem hstep_cells (v : Vtx) :
    (∃ m : Cell, (∀ C : Cell, owner C.val = v → C = m) ∧ (∀ C : Cell, ¬ owner C.val < v) ∧
      εC (Finsupp.single m 1) ≠ 0) ∨
    ∃ h : Cell → (Cell →₀ ℂ), (∀ C : Cell, owner C.val = v → ∀ D ∈ (h C).support,
        owner D.val = v) ∧
      ∀ C : Cell, owner C.val = v →
        (δC (h C)).filter (fun D => owner D.val = v) +
          Finsupp.linearCombination ℂ h ((δC (Finsupp.single C 1)).filter
            (fun D => owner D.val = v)) = Finsupp.single C 1 := by
  by_cases hd : ∃ j0 ∈ v.M, v.nb j0 < v
  · obtain ⟨j0, hj0, hdesc⟩ := hd
    right
    exact ⟨fun C => ofF (hF v j0 C.val), fun C hC D hD => owner_support_hF hdesc C hC D hD,
      fun C hC => cell_homotopy_identity hj0 hdesc C hC⟩
  · left
    have hd : ∀ ℓ ∈ v.M, ¬ v.nb ℓ < v := fun ℓ hℓ h => hd ⟨ℓ, hℓ, h⟩
    have hhigher : ∀ ℓ ∈ v.M, v < v.nb ℓ := fun ℓ hℓ =>
      lt_of_le_of_ne (not_lt.mp (hd ℓ hℓ)) (v.nb_ne hℓ).symm
    refine ⟨v.cell, fun C hC => ?_, fun C hlt => ?_, ?_⟩
    · obtain ⟨hsub, -⟩ := owner_spec C.isCell.1 C.isCell.2
      rw [hC] at hsub
      apply Cell.ext
      apply Finset.Subset.antisymm hsub
      intro ℓ hℓ
      by_contra hℓC
      exact hd ℓ hℓ ((owner_eq_iff C.isCell.1 hsub).mp hC ℓ hℓ hℓC)
    · exact absurd (v.le_of_neighbours_higher hhigher (owner C.val)) (not_le.mpr hlt)
    · rw [εC_single]
      show epsF v.M ≠ 0
      rw [epsF, ite_eq_left v.card_M]
      exact iota_epsMod_ne_zero v

/-- The augmented cellular chain complex of the well-rounded retract, with its `Γ(3)`-action. -/
def wellRounded : GradedComplexData principalLevel where
  X := Cell
  grade := Cell.grade
  grade_smul := Cell.grade_smul
  δ := δC
  δ_equivariant := δC_equivariant
  δ_δ := δC_δC
  δ_grade := δC_grade
  ε := εC
  ε_invariant := εC_invariant
  ε_δ := εC_δC
  ε_grade := εC_grade
  free := Cell.free
  grade_le := Cell.grade_le
  exact := fun z hz hε =>
    morse_exact δC δC_δC εC εC_δC (fun C : Cell => owner C.val) owner_le_of_support hstep_cells z
      hz hε
  surj := ⟨Vtx.base.cell, by
    rw [εC_single]
    show epsF Vtx.base.M ≠ 0
    rw [epsF, ite_eq_left Vtx.base.card_M]
    exact iota_epsMod_ne_zero Vtx.base⟩

end TernaryPeriodPolynomials.FreeResolution
