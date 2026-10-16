module

public import TernaryPeriodPolynomials.Building.OrientedChain.ListChains

@[expose] public section


noncomputable section
namespace TernaryPoly.OrientedChainJoin
open OrientedListChains
variable {V : Type*}

/-- A linear map from oriented chains is determined by its actual simplex values. -/
theorem chain_ext {E : Type*} [AddCommGroup E] [Module ℚ E]
    {f g : Chain V →ₗ[ℚ] E} (h : ∀ l, f (simplex l) = g (simplex l)) : f = g := by
  have he : f.comp (relations V).mkQ = g.comp (relations V).mkQ := by
    apply Finsupp.lhom_ext
    intro l q
    have hq : Finsupp.single l q = q • rawSimplex l := by simp [rawSimplex]
    simp only [hq,LinearMap.comp_apply,map_smul]
    exact congrArg (fun x => q • x) (h l)
  apply LinearMap.ext
  intro c
  refine Quotient.inductionOn' c (fun c => ?_)
  exact LinearMap.congr_fun he c

/-- Prefixing anticommutes in the actual alternating quotient. -/
theorem cons_anticommute (a b : V) (c : Chain V) :
    cons a (cons b c) + cons b (cons a c) = 0 := by
  have he : (cons a).comp (cons b) + (cons b).comp (cons a) =
      (0 : Chain V →ₗ[ℚ] Chain V) := by
    apply chain_ext
    intro l
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,cons_simplex,LinearMap.zero_apply]
      using simplex_swap a b l
  exact LinearMap.congr_fun he c

/-- The exact cone-boundary identity for every finite oriented chain. -/
theorem boundary_cons_chain (a : V) (c : Chain V) :
    boundary (cons a c) = c - cons a (boundary c) := by
  have he : boundary.comp (cons a) =
      LinearMap.id - (cons a).comp boundary := by
    apply chain_ext
    intro l
    simp only [LinearMap.comp_apply,cons_simplex,boundary_cons,
      LinearMap.sub_apply,LinearMap.id_apply]
  exact LinearMap.congr_fun he c

/-- Prefixing by a list, as a linear map on actual chains. -/
def prependList : List V → Chain V →ₗ[ℚ] Chain V
  | [] => LinearMap.id
  | a :: l => (cons a).comp (prependList l)

@[simp] theorem prefix_simplex (l m : List V) : prependList l (simplex m) = simplex (l ++ m) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [prependList,LinearMap.comp_apply,ih,cons_simplex,List.cons_append]

/-- The finite free linear extension of all prependList maps. -/
def rawJoin : Raw V →ₗ[ℚ] (Chain V →ₗ[ℚ] Chain V) :=
  Finsupp.lsum ℚ (fun l => LinearMap.toSpanSingleton ℚ _ (prependList l))

@[simp] theorem rawJoin_simplex (l : List V) : rawJoin (rawSimplex l) = prependList l := by
  simp [rawJoin,rawSimplex]

theorem rawJoin_rawCons (a : V) (c : Raw V) :
    rawJoin (rawCons a c) = (cons a).comp (rawJoin c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd,LinearMap.comp_add]
  | single l q =>
    have hq : Finsupp.single l q = q • rawSimplex l := by simp [rawSimplex]
    simp only [hq,map_smul,rawCons_simplex,rawJoin_simplex,prependList,LinearMap.comp_smul]

theorem rawJoin_relation {c : Raw V} (hc : c ∈ relations V) : rawJoin c = 0 := by
  induction hc with
  | swap a b l =>
    apply LinearMap.ext
    intro c
    simp only [map_add,LinearMap.add_apply,rawJoin_simplex,prependList,LinearMap.comp_apply,
      LinearMap.zero_apply]
    exact cons_anticommute a b (prependList l c)
  | cons a hc ih => rw [rawJoin_rawCons,ih,LinearMap.comp_zero]
  | zero => exact map_zero rawJoin
  | add hc hd ihc ihd => rw [map_add,ihc,ihd,add_zero]
  | smul q hc ih => rw [map_smul,ih,smul_zero]

/-- The actual bilinear join, descended from concatenation of finite vertex lists. -/
def join : Chain V →ₗ[ℚ] (Chain V →ₗ[ℚ] Chain V) :=
  (relations V).liftQ rawJoin (fun _ hc => rawJoin_relation hc)

@[simp] theorem join_simplex_left (l : List V) : join (simplex l) = prependList l := by
  change rawJoin (rawSimplex l) = prependList l
  exact rawJoin_simplex l

@[simp] theorem join_simplex (l m : List V) :
    join (simplex l) (simplex m) = simplex (l ++ m) := by
  rw [join_simplex_left,prefix_simplex]

theorem join_cons_left (a : V) (c d : Chain V) :
    join (cons a c) d = cons a (join c d) := by
  refine Quotient.inductionOn' c (fun c => ?_)
  change rawJoin (rawCons a c) d = cons a (rawJoin c d)
  rw [rawJoin_rawCons]
  rfl

/-- The graded boundary formula, with the sign given by the number of left vertices. -/
theorem boundary_join_simplex (l : List V) (c : Chain V) :
    boundary (join (simplex l) c) = join (boundary (simplex l)) c +
      (-1 : ℚ)^l.length • join (simplex l) (boundary c) := by
  induction l with
  | nil => simp [join_simplex_left,prependList,boundary_nil]
  | cons a l ih =>
    simp only [join_simplex_left,prependList,LinearMap.comp_apply] at ih ⊢
    rw [boundary_cons_chain,ih,boundary_cons,map_sub,LinearMap.sub_apply,join_cons_left]
    simp only [join_simplex_left,List.length_cons,pow_succ,mul_neg_one,neg_smul,
      map_add,map_smul]
    abel

/-- A chain supported on n-vertex faces has the same graded Leibniz sign. -/
theorem boundary_join_chains (C : PreAbstractSimplicialComplex V) (n : ℕ)
    {c : Chain V} (hc : c ∈ chains C n) (d : Chain V) :
    boundary (join c d) = join (boundary c) d + (-1 : ℚ)^n • join c (boundary d) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,_,rfl⟩ := hc
    simpa only [hlen] using boundary_join_simplex l d
  | zero => simp
  | add c e hc he ihc ihe =>
    simp only [map_add,LinearMap.add_apply,ihc,ihe,smul_add]
    abel
  | smul q c hc ih =>
    simp only [map_smul,LinearMap.smul_apply,ih,smul_add,smul_smul]
    rw [mul_comm q]

end TernaryPoly.OrientedChainJoin
