module

public import TernaryPeriodPolynomials.Building.Ambient.HighAdditiveElimination
public import TernaryPeriodPolynomials.Building.OrientedChain.SimplexPermutation
public import TernaryPeriodPolynomials.Building.OrientedChain.VertexExtraction
public import TernaryPeriodPolynomials.Building.BadFace.Contraction

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientHorizontalElimination
open ModThreeGoodAction AugmentedFrameComplex PrimitiveLineHeight AmbientHeightFiltration
open OrientedListChains OrientedChainJoin OrientedVertexExtraction OrientedSimplexPermutation
open OrientedChainProjection BadFaceContraction
local instance : DecidableEq RationalLine := Classical.decEq _

/-- The precise local geometry needed by the finite horizontal-edge surgery. -/
def PairGeometry (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) : Prop :=
  ∀ U V : RationalLine, U ≠ V → height F U = N → height F V = N →
    {U,V} ∈ ambient → ∃ D : RationalLine, height F D < N ∧
      ∀ W : RationalLine, [U,V,W].Nodup → Allowed (bounded F N) [U,V,W] →
        Module.finrank ℚ (faceSpan [U,V,W].toFinset) = 3 →
        Allowed (bounded F N) [D,U,V,W] ∧
        Module.finrank ℚ (faceSpan [D,U,W].toFinset) = 3 ∧
        Module.finrank ℚ (faceSpan [D,V,W].toFinset) = 3

/-- All ordered pairs of distinct high vertices of the simplex belong to this finite set. -/
def EdgesWithin (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (S : Finset (RationalLine × RationalLine)) (l : List RationalLine) : Prop :=
  ∀ U ∈ l, ∀ V ∈ l, U ≠ V → N ≤ height F U → N ≤ height F V → (U,V) ∈ S

/-- Reduced triangles with explicitly finite allowed high-edge support. -/
def restricted (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (S : Finset (RationalLine × RationalLine)) : Submodule ℚ (Chain RationalLine) :=
  Submodule.span ℚ {c | ∃ l : List RationalLine,
    l.length = 3 ∧ Allowed (bounded F N) l ∧ ReducedTriangle F N l ∧
      EdgesWithin F N S l ∧ simplex l = c}

theorem simplex_mem_restricted (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (S : Finset (RationalLine × RationalLine)) (l : List RationalLine)
    (hlen : l.length = 3) (ha : Allowed (bounded F N) l) (hr : ReducedTriangle F N l)
    (hs : EdgesWithin F N S l) : simplex l ∈ restricted F N S :=
  Submodule.subset_span ⟨l,hlen,ha,hr,hs,rfl⟩

theorem restricted_le_reduced (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (S : Finset (RationalLine × RationalLine)) : restricted F N S ≤ reducedTriangles F N := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l,hlen,ha,hr,_,rfl⟩
  exact simplex_mem_reducedTriangles F N l hlen ha hr

theorem restricted_mono (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    {S T : Finset (RationalLine × RationalLine)} (hst : S ⊆ T) :
    restricted F N S ≤ restricted F N T := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l,hlen,ha,hr,hs,rfl⟩
  exact simplex_mem_restricted F N T l hlen ha hr
    (fun U hU V hV hne hu hv => hst (hs U hU V hV hne hu hv))

/-- Finite span induction gives finite high-edge support for every actual reduced chain. -/
theorem exists_restricted (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    {c : Chain RationalLine} (hc : c ∈ reducedTriangles F N) :
    ∃ S : Finset (RationalLine × RationalLine), c ∈ restricted F N S := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,ha,hr,rfl⟩ := hc
    refine ⟨l.toFinset ×ˢ l.toFinset,simplex_mem_restricted F N _ l hlen ha hr ?_⟩
    intro U hU V hV _ _ _
    exact Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hU,List.mem_toFinset.mpr hV⟩
  | zero => exact ⟨∅,(restricted F N ∅).zero_mem⟩
  | add c d hc hd ihc ihd =>
    obtain ⟨S,hS⟩ := ihc
    obtain ⟨T,hT⟩ := ihd
    exact ⟨S ∪ T,(restricted F N (S ∪ T)).add_mem
      (restricted_mono F N Finset.subset_union_left hS)
      (restricted_mono F N Finset.subset_union_right hT)⟩
  | smul q c hc ih =>
    obtain ⟨S,hS⟩ := ih
    exact ⟨S,(restricted F N S).smul_mem q hS⟩

/-- A nondegenerate triangle containing two specified distinct vertices can be ordered by them. -/
theorem triangle_order_pair (l : List RationalLine) (hlen : l.length = 3)
    (hn : l.Nodup) (U V : RationalLine) (hne : U ≠ V) (hu : U ∈ l) (hv : V ∈ l) :
    ∃ W : RationalLine, l.Perm [U,V,W] := by
  have hp := List.perm_cons_erase hu
  have hv' : V ∈ l.erase U := (hn.mem_erase_iff).mpr ⟨Ne.symm hne,hv⟩
  have hp' := List.perm_cons_erase hv'
  have hh := hp.trans (hp'.cons U)
  have hlen' : ((l.erase U).erase V).length = 1 := by
    have he := hh.length_eq
    simp only [List.length_cons,hlen] at he
    omega
  obtain ⟨W,hW⟩ := List.length_eq_one_iff.mp hlen'
  exact ⟨W,by simpa only [hW] using hh⟩

/-- Contract the entire pair star, including incident triangles with three high vertices. -/
def pairCoefficient (U V : RationalLine) : Chain RationalLine →ₗ[ℚ] Chain RationalLine :=
  extract [U,V]

def pairPart (U V : RationalLine) : Chain RationalLine →ₗ[ℚ] Chain RationalLine :=
  (cons U).comp ((cons V).comp (pairCoefficient U V))

def pairFilling (D U V : RationalLine) : Chain RationalLine →ₗ[ℚ] Chain RationalLine :=
  (cons D).comp (pairPart U V)

/-- The two independent replacements, after the dependent common face cancels on cycles. -/
def pairRemainder (D U V : RationalLine) : Chain RationalLine →ₗ[ℚ] Chain RationalLine :=
  LinearMap.id - pairPart U V +
    (cons D).comp (((cons V) - (cons U)).comp (pairCoefficient U V))

theorem pairCoefficient_eq_zero_of_not_mem (U V : RationalLine) (l : List RationalLine)
    (h : U ∉ l ∨ V ∉ l) : pairCoefficient U V (simplex l) = 0 := by
  rcases h with h | h
  · change atVertex V (atVertex U (simplex l)) = 0
    rw [atVertex_simplex_of_not_mem U l h,map_zero]
  · have he := OrientedChainContraction.contraction_anticommute
      (vertexWeight V) (vertexWeight U) (simplex l)
    change atVertex V (atVertex U (simplex l)) + atVertex U (atVertex V (simplex l)) = 0 at he
    rw [atVertex_simplex_of_not_mem V l h,map_zero,add_zero] at he
    exact he

theorem pairCoefficient_ordered (U V W : RationalLine) (hn : [U,V,W].Nodup) :
    pairCoefficient U V (simplex [U,V,W]) = simplex [W] := by
  change extract [U,V] (simplex ([U,V] ++ [W])) = simplex [W]
  rw [← join_simplex]
  apply extract_join [U,V] (by simpa using hn.sublist (by simp : [U,V].Sublist [U,V,W]))
  intro A hA
  apply atVertex_simplex_of_not_mem
  have huw : U ≠ W := fun he => (List.nodup_cons.mp hn).1 (by simp [he])
  have hvw : V ≠ W := by simpa using (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hA
  rcases hA with rfl | rfl
  · simpa using huw
  · simpa using hvw

theorem pairFilling_ordered (D U V W : RationalLine) (hn : [U,V,W].Nodup) :
    pairFilling D U V (simplex [U,V,W]) = simplex [D,U,V,W] := by
  simp only [pairFilling,pairPart,LinearMap.comp_apply,pairCoefficient_ordered U V W hn,cons_simplex]

theorem pairRemainder_ordered (D U V W : RationalLine) (hn : [U,V,W].Nodup) :
    pairRemainder D U V (simplex [U,V,W]) = simplex [D,V,W] - simplex [D,U,W] := by
  simp only [pairRemainder,pairPart,LinearMap.comp_apply,LinearMap.add_apply,
    LinearMap.sub_apply,LinearMap.id_apply,pairCoefficient_ordered U V W hn,cons_simplex,
    sub_self,zero_add,map_sub]

theorem pair_surgery_identity (D U V : RationalLine) (c : Chain RationalLine)
    (hd : boundary c = 0) : c = boundary (pairFilling D U V c) + pairRemainder D U V c := by
  have he := extract_boundary [U,V] c
  simp only [hd,map_zero,List.length_cons,List.length_nil,pow_succ,pow_zero] at he
  have hz : boundary (pairCoefficient U V c) = 0 := by simpa [pairCoefficient] using he.symm
  simp only [pairFilling,pairPart,pairRemainder,LinearMap.comp_apply,LinearMap.add_apply,
    LinearMap.sub_apply,LinearMap.id_apply,boundary_cons_chain,map_sub,hz,map_zero,sub_zero]
  abel

/-- Ordered simplex support and reducedness are unchanged by permutation. -/
theorem allowed_perm {l m : List RationalLine} (hp : l.Perm m)
    {F : IntegralVector →ₗ[ℤ] ℤ} {N : ℕ} (ha : Allowed (bounded F N) l) :
    Allowed (bounded F N) m := by
  rcases ha with rfl | ha
  · exact Or.inl (List.perm_nil.mp hp.symm)
  · right
    convert ha using 1
    ext A
    simpa only [List.mem_toFinset] using (hp.mem_iff (a := A)).symm

theorem reduced_perm {l m : List RationalLine} (hp : l.Perm m)
    {F : IntegralVector →ₗ[ℤ] ℤ} {N : ℕ} (hr : ReducedTriangle F N l) :
    ReducedTriangle F N m := by
  have he : l.toFinset = m.toFinset := by ext A; simp only [List.mem_toFinset,hp.mem_iff]
  rcases hr with hr | hr
  · exact Or.inl (he ▸ hr)
  · exact Or.inr (fun A hA => hr A (hp.mem_iff.mpr hA))

theorem edgesWithin_perm {l m : List RationalLine} (hp : l.Perm m)
    {F : IntegralVector →ₗ[ℤ] ℤ} {N : ℕ} {S : Finset (RationalLine × RationalLine)}
    (hs : EdgesWithin F N S l) : EdgesWithin F N S m :=
  fun U hU V hV => hs U (hp.mem_iff.mpr hU) V (hp.mem_iff.mpr hV)

/-- Inserting a low vertex creates no high pair, while omitted endpoints erase the chosen pair. -/
theorem edgesWithin_replacement (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (S : Finset (RationalLine × RationalLine)) (U V D : RationalLine)
    (l m : List RationalLine) (hs : EdgesWithin F N S l) (hd : height F D < N)
    (hsub : ∀ A ∈ m, A = D ∨ A ∈ l) (homit : U ∉ m ∨ V ∉ m) :
    EdgesWithin F N (S.erase (U,V)) m := by
  intro A hA B hB hne hAH hBH
  have hAl : A ∈ l := (hsub A hA).resolve_left (fun he => by subst A; omega)
  have hBl : B ∈ l := (hsub B hB).resolve_left (fun he => by subst B; omega)
  apply Finset.mem_erase.mpr
  refine ⟨?_,hs A hAl B hBl hne hAH hBH⟩
  intro he
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
  exact homit.elim (fun h => h hA) (fun h => h hB)

theorem pairFilling_absent (D U V : RationalLine) (l : List RationalLine)
    (h : U ∉ l ∨ V ∉ l) : pairFilling D U V (simplex l) = 0 := by
  simp only [pairFilling,pairPart,LinearMap.comp_apply,
    pairCoefficient_eq_zero_of_not_mem U V l h,map_zero]

theorem pairRemainder_absent (D U V : RationalLine) (l : List RationalLine)
    (h : U ∉ l ∨ V ∉ l) : pairRemainder D U V (simplex l) = simplex l := by
  simp only [pairRemainder,pairPart,LinearMap.comp_apply,LinearMap.add_apply,
    LinearMap.sub_apply,LinearMap.id_apply,pairCoefficient_eq_zero_of_not_mem U V l h,
    map_zero,sub_zero,add_zero]

/-- Exact supported replacement of an ordered incident triangle. -/
theorem ordered_replacements_mem (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (S : Finset (RationalLine × RationalLine)) (U V D W : RationalLine)
    (hn : [U,V,W].Nodup) (hu : height F U = N) (hv : height F V = N)
    (hd : height F D < N) (hs : EdgesWithin F N S [U,V,W])
    (ht : Allowed (bounded F N) [D,U,V,W])
    (hru : Module.finrank ℚ (faceSpan [D,U,W].toFinset) = 3)
    (hrv : Module.finrank ℚ (faceSpan [D,V,W].toFinset) = 3) :
    pairFilling D U V (simplex [U,V,W]) ∈ chains (bounded F N) 4 ∧
      pairRemainder D U V (simplex [U,V,W]) ∈ restricted F N (S.erase (U,V)) := by
  have hne : U ≠ V := fun he => (List.nodup_cons.mp hn).1 (by simp [he])
  have hdu : D ≠ U := by intro he; subst D; omega
  have hdv : D ≠ V := by intro he; subst D; omega
  have huw : U ≠ W := fun he => (List.nodup_cons.mp hn).1 (by simp [he])
  have hvw : V ≠ W := by simpa using (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  have hsu : EdgesWithin F N (S.erase (U,V)) [D,U,W] :=
    edgesWithin_replacement F N S U V D [U,V,W] [D,U,W] hs hd
      (by
        intro A hA
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hA
        rcases hA with rfl | rfl | rfl <;> simp)
      (Or.inr (by simp [Ne.symm hdv,Ne.symm hne,hvw]))
  have hsv : EdgesWithin F N (S.erase (U,V)) [D,V,W] :=
    edgesWithin_replacement F N S U V D [U,V,W] [D,V,W] hs hd
      (by
        intro A hA
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hA
        rcases hA with rfl | rfl | rfl <;> simp)
      (Or.inl (by simp [Ne.symm hdu,hne,huw]))
  have hmu := simplex_mem_restricted F N (S.erase (U,V)) [D,U,W] rfl
    (allowed_sublist _ ht (by simp : [D,U,W].Sublist [D,U,V,W])) (Or.inl hru) hsu
  have hmv := simplex_mem_restricted F N (S.erase (U,V)) [D,V,W] rfl
    (allowed_sublist _ ht (by simp : [D,V,W].Sublist [D,U,V,W])) (Or.inl hrv) hsv
  rw [pairFilling_ordered D U V W hn,pairRemainder_ordered D U V W hn]
  exact ⟨simplex_mem_chains (bounded F N) [D,U,V,W] ht,
    (restricted F N (S.erase (U,V))).sub_mem hmv hmu⟩

theorem pair_surgery_simplex_mem (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (S : Finset (RationalLine × RationalLine)) (U V D : RationalLine)
    (hne : U ≠ V) (hu : height F U = N) (hv : height F V = N) (hd : height F D < N)
    (hgeom : ∀ W : RationalLine, [U,V,W].Nodup → Allowed (bounded F N) [U,V,W] →
      Module.finrank ℚ (faceSpan [U,V,W].toFinset) = 3 →
      Allowed (bounded F N) [D,U,V,W] ∧
      Module.finrank ℚ (faceSpan [D,U,W].toFinset) = 3 ∧
      Module.finrank ℚ (faceSpan [D,V,W].toFinset) = 3)
    (l : List RationalLine) (hlen : l.length = 3) (ha : Allowed (bounded F N) l)
    (hr : ReducedTriangle F N l) (hs : EdgesWithin F N S l) :
    pairFilling D U V (simplex l) ∈ chains (bounded F N) 4 ∧
      pairRemainder D U V (simplex l) ∈ restricted F N (S.erase (U,V)) := by
  classical
  by_cases hn : l.Nodup
  · by_cases hpair : U ∈ l ∧ V ∈ l
    · obtain ⟨W,hp⟩ := triangle_order_pair l hlen hn U V hne hpair.1 hpair.2
      have hn' : [U,V,W].Nodup := hp.nodup_iff.mp hn
      have ha' := allowed_perm hp ha
      have hr' := reduced_perm hp hr
      have hs' := edgesWithin_perm hp hs
      have hfull : Module.finrank ℚ (faceSpan [U,V,W].toFinset) = 3 := by
        rcases hr' with hr' | hr'
        · exact hr'
        · have hh := hr' U (by simp)
          omega
      obtain ⟨ht,hru,hrv⟩ := hgeom W hn' ha' hfull
      obtain ⟨ht',hr'⟩ := ordered_replacements_mem F N S U V D W hn' hu hv hd hs' ht hru hrv
      obtain ⟨q,hq⟩ := simplex_perm_smul hp
      rw [hq,map_smul,map_smul]
      exact ⟨(chains (bounded F N) 4).smul_mem q ht',
        (restricted F N (S.erase (U,V))).smul_mem q hr'⟩
    · have habsent : U ∉ l ∨ V ∉ l := not_and_or.mp hpair
      rw [pairFilling_absent D U V l habsent,pairRemainder_absent D U V l habsent]
      refine ⟨(chains (bounded F N) 4).zero_mem,
        simplex_mem_restricted F N _ l hlen ha hr ?_⟩
      exact edgesWithin_replacement F N S U V D l l hs hd
        (fun A hA => Or.inr hA) habsent
  · rw [simplex_eq_zero_of_not_nodup l hn,map_zero,map_zero]
    exact ⟨(chains (bounded F N) 4).zero_mem,(restricted F N (S.erase (U,V))).zero_mem⟩

theorem pair_surgery_mem (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (S : Finset (RationalLine × RationalLine)) (U V D : RationalLine)
    (hne : U ≠ V) (hu : height F U = N) (hv : height F V = N) (hd : height F D < N)
    (hgeom : ∀ W : RationalLine, [U,V,W].Nodup → Allowed (bounded F N) [U,V,W] →
      Module.finrank ℚ (faceSpan [U,V,W].toFinset) = 3 →
      Allowed (bounded F N) [D,U,V,W] ∧
      Module.finrank ℚ (faceSpan [D,U,W].toFinset) = 3 ∧
      Module.finrank ℚ (faceSpan [D,V,W].toFinset) = 3)
    {c : Chain RationalLine} (hc : c ∈ restricted F N S) :
    pairFilling D U V c ∈ chains (bounded F N) 4 ∧
      pairRemainder D U V c ∈ restricted F N (S.erase (U,V)) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,ha,hr,hs,rfl⟩ := hc
    exact pair_surgery_simplex_mem F N S U V D hne hu hv hd hgeom l hlen ha hr hs
  | zero => simpa only [map_zero] using
      And.intro (chains (bounded F N) 4).zero_mem (restricted F N (S.erase (U,V))).zero_mem
  | add c d hc hd ihc ihd =>
    simpa only [map_add] using And.intro
      ((chains (bounded F N) 4).add_mem ihc.1 ihd.1)
      ((restricted F N (S.erase (U,V))).add_mem ihc.2 ihd.2)
  | smul q c hc ih =>
    simpa only [map_smul] using And.intro
      ((chains (bounded F N) 4).smul_mem q ih.1)
      ((restricted F N (S.erase (U,V))).smul_mem q ih.2)

/-- A high pair occurring in a bounded simplex is an actual horizontal ambient edge. -/
theorem pair_admissible_of_occurs (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (l : List RationalLine) (ha : Allowed (bounded F N) l)
    (U V : RationalLine) (hU : U ∈ l) (hV : V ∈ l) (hne : U ≠ V)
    (hu : N ≤ height F U) (hv : N ≤ height F V) :
    U ≠ V ∧ height F U = N ∧ height F V = N ∧ {U,V} ∈ ambient := by
  obtain ⟨ha,hb⟩ := (allowed_bounded_iff F N l).mp ha
  refine ⟨hne,le_antisymm (hb U hU) hu,le_antisymm (hb V hV) hv,?_⟩
  have hf := ha.resolve_left (fun he => by subst l; simp at hU)
  apply (ambient.isRelLowerSet_faces hf).2 ?_ (by simp)
  intro A hA
  simp only [Finset.mem_insert,Finset.mem_singleton] at hA
  rcases hA with rfl | rfl
  · exact List.mem_toFinset.mpr hU
  · exact List.mem_toFinset.mpr hV

/-- An inadmissible pair never occurs as a high pair on an actual supported generator. -/
theorem restricted_erase_inadmissible (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (S : Finset (RationalLine × RationalLine)) (U V : RationalLine)
    (hnot : ¬(U ≠ V ∧ height F U = N ∧ height F V = N ∧ {U,V} ∈ ambient)) :
    restricted F N S ≤ restricted F N (S.erase (U,V)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l,hlen,ha,hr,hs,rfl⟩
  apply simplex_mem_restricted F N _ l hlen ha hr
  intro A hA B hB hne hu hv
  apply Finset.mem_erase.mpr
  refine ⟨?_,hs A hA B hB hne hu hv⟩
  intro he
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
  exact hnot (pair_admissible_of_occurs F N l ha A B hA hB hne hu hv)

/-- One entire horizontal pair-star is removed by a finite bounded filling. -/
theorem erase_pair (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (hg : PairGeometry F N)
    (S : Finset (RationalLine × RationalLine)) (U V : RationalLine)
    {c : Chain RationalLine} (hc : c ∈ restricted F N S) (hd : boundary c = 0) :
    ∃ t r : Chain RationalLine, t ∈ chains (bounded F N) 4 ∧
      r ∈ restricted F N (S.erase (U,V)) ∧ boundary r = 0 ∧ c = boundary t + r := by
  classical
  by_cases ha : U ≠ V ∧ height F U = N ∧ height F V = N ∧ {U,V} ∈ ambient
  · obtain ⟨D,hD,hgeom⟩ := hg U V ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
    obtain ⟨ht,hr⟩ := pair_surgery_mem F N S U V D ha.1 ha.2.1 ha.2.2.1 hD hgeom hc
    have he := pair_surgery_identity D U V c hd
    refine ⟨pairFilling D U V c,pairRemainder D U V c,ht,hr,?_,he⟩
    have he' := congrArg boundary he
    simpa only [hd,map_add,boundary_squared,zero_add] using he'.symm
  · exact ⟨0,c,(chains (bounded F N) 4).zero_mem,
      restricted_erase_inadmissible F N S U V ha hc,hd,by simp⟩

/-- Finite induction eliminates every allowed high pair without creating any new one. -/
theorem eliminate_restricted (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (hg : PairGeometry F N)
    (S : Finset (RationalLine × RationalLine))
    {c : Chain RationalLine} (hc : c ∈ restricted F N S) (hd : boundary c = 0) :
    ∃ t r : Chain RationalLine, t ∈ chains (bounded F N) 4 ∧
      r ∈ restricted F N ∅ ∧ boundary r = 0 ∧ c = boundary t + r := by
  classical
  induction S using Finset.induction_on generalizing c with
  | empty => exact ⟨0,c,(chains (bounded F N) 4).zero_mem,hc,hd,by simp⟩
  | @insert e S he ih =>
    obtain ⟨t,r,ht,hr,hdR,hcR⟩ := erase_pair F N hg (insert e S) e.1 e.2 hc hd
    have hr' : r ∈ restricted F N S := by simpa only [Prod.eta,Finset.erase_insert he] using hr
    obtain ⟨t',r',ht',hr',hdR',hrR'⟩ := ih hr' hdR
    refine ⟨t+t',r',(chains (bounded F N) 4).add_mem ht ht',hr',hdR',?_⟩
    rw [map_add,hcR,hrR']
    abel

/-- With no allowed high edge, every generator has at most one high vertex. -/
theorem restricted_empty_projection (F : IntegralVector →ₗ[ℤ] ℤ) (N k : ℕ) (hk : 2 ≤ k)
    {c : Chain RationalLine} (hc : c ∈ restricted F N ∅) :
    badCountProjection (fun L => height F L < N) k c = 0 := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,_,_,hs,rfl⟩ := hc
    have hb : badCount (fun L => height F L < N) l ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro U hU V hV
      obtain ⟨hUl,hUH⟩ := (mem_badVertices _ _ _).mp hU
      obtain ⟨hVl,hVH⟩ := (mem_badVertices _ _ _).mp hV
      by_contra hne
      exact Finset.notMem_empty (U,V) (hs U hUl V hVl hne
        (Nat.le_of_not_gt hUH) (Nat.le_of_not_gt hVH))
    have hne : badCount (fun L => height F L < N) l ≠ k := by omega
    rw [badCountProjection_simplex,ite_eq_right hne]
  | zero => exact map_zero _
  | add c d hc hd ihc ihd => rw [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => rw [map_smul,ih,smul_zero]

/-- Every bounded reduced two-cycle is homologous to a reduced cycle with at most one high vertex. -/
theorem eliminate_horizontal (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (hg : PairGeometry F N)
    {c : Chain RationalLine} (hc : c ∈ reducedTriangles F N) (hd : boundary c = 0) :
    ∃ t r : Chain RationalLine, t ∈ chains (bounded F N) 4 ∧
      r ∈ reducedTriangles F N ∧ boundary r = 0 ∧ c = boundary t + r ∧
      ∀ k : ℕ, 2 ≤ k → badCountProjection (fun L => height F L < N) k r = 0 := by
  obtain ⟨S,hS⟩ := exists_restricted F N hc
  obtain ⟨t,r,ht,hr,hdR,he⟩ := eliminate_restricted F N hg S hS hd
  exact ⟨t,r,ht,restricted_le_reduced F N ∅ hr,hdR,he,
    fun k hk => restricted_empty_projection F N k hk hr⟩

end TernaryPoly.AmbientHorizontalElimination
