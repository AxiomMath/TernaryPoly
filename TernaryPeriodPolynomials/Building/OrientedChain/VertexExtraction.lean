module

public import TernaryPeriodPolynomials.Building.OrientedChain.ChainContraction

@[expose] public section


noncomputable section
namespace TernaryPoly.OrientedVertexExtraction
open OrientedListChains OrientedChainJoin OrientedChainContraction
variable {V : Type*}

/-- The weighted join boundary formula for an arbitrary vertex covector. -/
theorem contraction_join_simplex (w : V → ℚ) (l : List V) (c : Chain V) :
    contraction w (join (simplex l) c) = join (contraction w (simplex l)) c +
      (-1 : ℚ)^l.length • join (simplex l) (contraction w c) := by
  induction l with
  | nil => simp [join_simplex_left,prependList]
  | cons a l ih =>
    simp only [join_simplex_left,prependList,LinearMap.comp_apply] at ih ⊢
    rw [contraction_cons_chain,ih,contraction_cons,map_sub,LinearMap.sub_apply,
      map_smul,LinearMap.smul_apply,join_cons_left]
    simp only [join_simplex_left,List.length_cons,pow_succ,mul_neg_one,neg_smul,
      map_add,map_smul]
    abel

/-- The coordinate covector belonging to one literal vertex. -/
def vertexWeight (a : V) : V → ℚ := by
  classical
  exact fun b => if b = a then 1 else 0

def atVertex (a : V) : Chain V →ₗ[ℚ] Chain V := contraction (vertexWeight a)

@[simp] theorem vertexWeight_self (a : V) : vertexWeight a a = 1 := by simp [vertexWeight]
@[simp] theorem vertexWeight_ne (a b : V) (h : b ≠ a) : vertexWeight a b = 0 := by
  simp [vertexWeight,h]

theorem atVertex_cons_self (a : V) (c : Chain V) :
    atVertex a (cons a c) = c - cons a (atVertex a c) := by
  simp only [atVertex,contraction_cons_chain,vertexWeight_self,one_smul]

theorem atVertex_cons_ne (a b : V) (h : b ≠ a) (c : Chain V) :
    atVertex a (cons b c) = -cons b (atVertex a c) := by
  simp only [atVertex,contraction_cons_chain,vertexWeight_ne a b h,zero_smul,zero_sub]

theorem atVertex_simplex_of_not_mem (a : V) (l : List V) (h : a ∉ l) :
    atVertex a (simplex l) = 0 := by
  apply contraction_simplex_eq_zero
  intro b hb
  exact vertexWeight_ne a b (fun he => h (he ▸ hb))

theorem atVertex_join_of_not_mem (a : V) (l : List V) (h : a ∉ l) (c : Chain V)
    (hc : atVertex a c = 0) : atVertex a (join (simplex l) c) = 0 := by
  rw [atVertex,contraction_join_simplex]
  change join (atVertex a (simplex l)) c + (-1 : ℚ)^l.length • join (simplex l) (atVertex a c) = 0
  rw [atVertex_simplex_of_not_mem a l h,hc,map_zero,map_zero,LinearMap.zero_apply,smul_zero,add_zero]

theorem cons_atVertex_of_cons_eq_zero (a : V) (c : Chain V) (hc : cons a c = 0) :
    cons a (atVertex a c) = c := by
  have h := atVertex_cons_self a c
  rw [hc,map_zero] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- Extract a list of vertices in its exact oriented order. -/
def extract : List V → Chain V →ₗ[ℚ] Chain V
  | [] => LinearMap.id
  | a :: l => (extract l).comp (atVertex a)

/-- Exact bad-face extraction is a left inverse on chains avoiding the extracted vertices. -/
theorem extract_join (l : List V) (hl : l.Nodup) (c : Chain V)
    (hc : ∀ a ∈ l, atVertex a c = 0) : extract l (join (simplex l) c) = c := by
  induction l with
  | nil => simp [extract,join_simplex_left,prependList]
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hl
    have hc_a := hc a (List.mem_cons_self)
    have hz := atVertex_join_of_not_mem a l ha c hc_a
    rw [← cons_simplex,join_cons_left]
    change extract l (atVertex a (cons a (join (simplex l) c))) = c
    rw [atVertex_cons_self,hz,map_zero,sub_zero]
    exact ih hl (fun b hb => hc b (List.mem_cons_of_mem a hb))

/-- A chain containing each listed vertex factors through the oriented join by that face. -/
theorem join_extract (l : List V) (hl : l.Nodup) (c : Chain V)
    (hc : ∀ a ∈ l, cons a c = 0) : join (simplex l) (extract l c) = c := by
  induction l generalizing c with
  | nil => simp [extract,join_simplex_left,prependList]
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hl
    have hc_a := hc a (List.mem_cons_self)
    have hrest : ∀ b ∈ l, cons b (atVertex a c) = 0 := by
      intro b hb
      have hba : b ≠ a := fun he => ha (he ▸ hb)
      have h := atVertex_cons_ne a b hba c
      rw [hc b (List.mem_cons_of_mem a hb),map_zero] at h
      exact neg_eq_zero.mp h.symm
    rw [← cons_simplex,join_cons_left]
    change cons a (join (simplex l) (extract l (atVertex a c))) = c
    rw [ih hl (atVertex a c) hrest]
    exact cons_atVertex_of_cons_eq_zero a c hc_a

/-- Joining a fixed nonrepeated face is injective on chains with no vertex in that face. -/
theorem join_injective_on (l : List V) (hl : l.Nodup) {c d : Chain V}
    (hc : ∀ a ∈ l, atVertex a c = 0) (hd : ∀ a ∈ l, atVertex a d = 0)
    (he : join (simplex l) c = join (simplex l) d) : c = d := by
  have h := congrArg (extract l) he
  simpa only [extract_join l hl c hc,extract_join l hl d hd] using h

/-- Exact extraction anticommutes with boundary once for each extracted vertex. -/
theorem extract_boundary (l : List V) (c : Chain V) :
    extract l (boundary c) = (-1 : ℚ)^l.length • boundary (extract l c) := by
  induction l generalizing c with
  | nil => simp [extract]
  | cons a l ih =>
    change extract l (atVertex a (boundary c)) = _
    rw [show atVertex a (boundary c) = -boundary (atVertex a c) from
      contraction_boundary (vertexWeight a) c,map_neg,ih]
    simp only [List.length_cons,pow_succ,mul_neg_one,neg_smul,extract,LinearMap.comp_apply]

end TernaryPoly.OrientedVertexExtraction
