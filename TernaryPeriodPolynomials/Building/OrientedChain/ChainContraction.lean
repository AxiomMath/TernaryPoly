module

public import TernaryPeriodPolynomials.Building.OrientedChain.ChainJoin

@[expose] public section


noncomputable section
namespace TernaryPoly.OrientedChainContraction
open OrientedListChains OrientedChainJoin
variable {V : Type*}

/-- Alternating vertex deletion, weighted by an arbitrary rational function. -/
def rawContractionList (w : V → ℚ) : List V → Raw V
  | [] => 0
  | a :: l => w a • rawSimplex l - rawCons a (rawContractionList w l)

def rawContraction (w : V → ℚ) : Raw V →ₗ[ℚ] Raw V :=
  Finsupp.lsum ℚ (fun l => LinearMap.toSpanSingleton ℚ _ (rawContractionList w l))

@[simp] theorem rawContraction_simplex (w : V → ℚ) (l : List V) :
    rawContraction w (rawSimplex l) = rawContractionList w l := by
  simp [rawContraction,rawSimplex]

theorem rawContraction_cons (w : V → ℚ) (a : V) (l : List V) :
    rawContraction w (rawSimplex (a :: l)) =
      w a • rawSimplex l - rawCons a (rawContraction w (rawSimplex l)) := by
  simp only [rawContraction_simplex,rawContractionList]

theorem rawContraction_rawCons (w : V → ℚ) (a : V) (c : Raw V) :
    rawContraction w (rawCons a c) = w a • c - rawCons a (rawContraction w c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add,hc,hd,smul_add]
    abel
  | single l q =>
    have hq : Finsupp.single l q = q • rawSimplex l := by simp [rawSimplex]
    simp only [hq,map_smul,rawCons_simplex,rawContraction_cons,smul_sub,smul_smul]
    rw [mul_comm q]

theorem rawContraction_relation (w : V → ℚ) {c : Raw V} (hc : c ∈ relations V) :
    rawContraction w c ∈ relations V := by
  induction hc with
  | swap a b l =>
    have h := rawCons_swap_relation a b (rawContraction w (rawSimplex l))
    convert h using 1
    simp only [map_add,rawContraction_cons,map_sub,map_smul,rawCons_simplex]
    abel
  | cons a hc ih =>
    rw [rawContraction_rawCons]
    exact (relations V).sub_mem ((relations V).smul_mem (w a) hc) (rawCons_relation a ih)
  | zero => simp
  | add hc hd ihc ihd => simpa only [map_add] using (relations V).add_mem ihc ihd
  | smul q hc ih => simpa only [map_smul] using (relations V).smul_mem q ih

/-- The actual weighted contraction on the oriented quotient. -/
def contraction (w : V → ℚ) : Chain V →ₗ[ℚ] Chain V :=
  (relations V).mapQ (relations V) (rawContraction w)
    (fun _ hc => rawContraction_relation w hc)

@[simp] theorem contraction_nil (w : V → ℚ) : contraction w (simplex []) = 0 := by
  change (relations V).mkQ (rawContraction w (rawSimplex [])) = 0
  simp [rawContractionList]

theorem contraction_cons (w : V → ℚ) (a : V) (l : List V) :
    contraction w (simplex (a :: l)) =
      w a • simplex l - cons a (contraction w (simplex l)) := by
  change (relations V).mkQ (rawContraction w (rawSimplex (a :: l))) = _
  rw [rawContraction_cons,map_sub,map_smul]
  rfl

theorem contraction_cons_chain (w : V → ℚ) (a : V) (c : Chain V) :
    contraction w (cons a c) = w a • c - cons a (contraction w c) := by
  have he : (contraction w).comp (cons a) =
      w a • LinearMap.id - (cons a).comp (contraction w) := by
    apply chain_ext
    intro l
    simp only [LinearMap.comp_apply,cons_simplex,contraction_cons,
      LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply]
  exact LinearMap.congr_fun he c

/-- Any two actual contractions anticommute. -/
theorem contraction_anticommute (u w : V → ℚ) (c : Chain V) :
    contraction u (contraction w c) + contraction w (contraction u c) = 0 := by
  have he : (contraction u).comp (contraction w) + (contraction w).comp (contraction u) =
      (0 : Chain V →ₗ[ℚ] Chain V) := by
    apply chain_ext
    intro l
    change contraction u (contraction w (simplex l)) +
      contraction w (contraction u (simplex l)) = 0
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [contraction_cons,map_sub,map_smul,contraction_cons_chain]
      calc
        _ = cons a (contraction u (contraction w (simplex l)) +
            contraction w (contraction u (simplex l))) := by rw [map_add]; abel
        _ = 0 := by rw [ih,map_zero]
  exact LinearMap.congr_fun he c

theorem contraction_squared (w : V → ℚ) (c : Chain V) :
    contraction w (contraction w c) = 0 := by
  have h : (2 : ℚ) • contraction w (contraction w c) = 0 := by
    simpa only [two_smul] using contraction_anticommute w w c
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

/-- The ordinary augmented boundary is the constant-one contraction. -/
theorem contraction_one : contraction (fun _ : V => 1) = boundary := by
  apply chain_ext
  intro l
  induction l with
  | nil => simp
  | cons a l ih => simp only [contraction_cons,one_smul,boundary_cons,ih]

theorem contraction_boundary (w : V → ℚ) (c : Chain V) :
    contraction w (boundary c) = -boundary (contraction w c) := by
  have h := contraction_anticommute w (fun _ => 1) c
  rw [contraction_one] at h
  exact eq_neg_of_add_eq_zero_left h

/-- A contraction supported outside a simplex is zero on that simplex. -/
theorem contraction_simplex_eq_zero (w : V → ℚ) (l : List V)
    (h : ∀ a ∈ l, w a = 0) : contraction w (simplex l) = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [contraction_cons,h a (List.mem_cons_self),zero_smul,
      ih (fun b hb => h b (List.mem_cons_of_mem a hb)),map_zero,sub_self]

/-- Contraction lowers the vertex degree and preserves actual simplex support. -/
theorem contraction_simplex_mem (w : V → ℚ) (S : Submodule ℚ (Chain V)) (l : List V)
    (h : ∀ m : List V, m.Sublist l → m.length + 1 = l.length → simplex m ∈ S) :
    contraction w (simplex l) ∈ S := by
  induction l generalizing S with
  | nil => simp only [contraction_nil]; exact S.zero_mem
  | cons a l ih =>
    rw [contraction_cons]
    apply S.sub_mem
    · exact S.smul_mem _ (h l (List.sublist_cons_self a l) rfl)
    · apply ih (S.comap (cons a))
      intro m hm hlen
      change cons a (simplex m) ∈ S
      rw [cons_simplex]
      exact h (a :: m) (hm.cons_cons a) (congrArg Nat.succ hlen)

theorem contraction_mem_chains (w : V → ℚ) (C : PreAbstractSimplicialComplex V) (n : ℕ)
    {c : Chain V} (hc : c ∈ chains C (n+1)) : contraction w c ∈ chains C n := by
  change c ∈ (chains C n).comap (contraction w)
  apply (Submodule.span_le.mpr ?_) hc
  rintro _ ⟨l,hlen,hl,rfl⟩
  change contraction w (simplex l) ∈ chains C n
  apply contraction_simplex_mem
  intro m hm hmlen
  have hm_len : m.length = n := Nat.add_right_cancel (hmlen.trans hlen)
  simpa only [hm_len] using simplex_mem_chains C m (allowed_sublist C hl hm)

end TernaryPoly.OrientedChainContraction
