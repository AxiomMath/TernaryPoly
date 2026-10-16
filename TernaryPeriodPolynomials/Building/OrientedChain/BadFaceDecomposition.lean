module

public import TernaryPeriodPolynomials.Building.OrientedChain.VertexExtraction
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainProjection

@[expose] public section

noncomputable section
namespace TernaryPoly.OrientedBadFaceDecomposition
open OrientedListChains OrientedChainJoin OrientedVertexExtraction OrientedChainProjection
variable {V : Type*}
local instance : DecidableEq V := Classical.decEq V

/-- A finite representative supplies an explicit finite simplex expansion in the quotient. -/
theorem mkQ_expansion (r : Raw V) :
    (relations V).mkQ r = ∑ l ∈ r.support, r l • simplex l := by
  have h := congrArg ((relations V).mkQ) (Finsupp.sum_single r)
  simp only [Finsupp.sum,map_sum] at h
  have hs (l : List V) (q : ℚ) : (relations V).mkQ (Finsupp.single l q) = q • simplex l := by
    have hq : Finsupp.single l q = q • rawSimplex l := by simp [rawSimplex]
    rw [hq,map_smul]
    rfl
  simp_rw [hs] at h
  exact h.symm

/-- Summing the bad-face projections over a representative's finite support recovers the chain. -/
theorem sum_badFaceProjection_raw (G : V → Prop) (r : Raw V) (S : Finset (Finset V))
    (hS : ∀ l ∈ r.support, badVertices G l ∈ S) :
    ∑ s ∈ S, badFaceProjection G s ((relations V).mkQ r) = (relations V).mkQ r := by
  classical
  rw [mkQ_expansion]
  simp only [map_sum,map_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← Finset.smul_sum]
  congr 1
  simp [hS l hl]

/-- Outside that finite source support, the corresponding bad-face projection is zero. -/
theorem badFaceProjection_raw_eq_zero (G : V → Prop) (r : Raw V) (s : Finset V)
    (hs : ∀ l ∈ r.support, badVertices G l ≠ s) :
    badFaceProjection G s ((relations V).mkQ r) = 0 := by
  classical
  rw [mkQ_expansion]
  simp only [map_sum,map_smul]
  apply Finset.sum_eq_zero
  intro l hl
  simp only [badFaceProjection_simplex,hs l hl,ite_false,smul_zero]

/-- Every actual oriented chain has a finite, exact, orthogonal bad-face decomposition. -/
theorem exists_badFace_decomposition (G : V → Prop) (c : Chain V) :
    ∃ S : Finset (Finset V),
      (∑ s ∈ S, badFaceProjection G s c) = c ∧
      ∀ s ∉ S, badFaceProjection G s c = 0 := by
  classical
  refine Quotient.inductionOn' c (fun r => ?_)
  let S := r.support.image (badVertices G)
  refine ⟨S,sum_badFaceProjection_raw G r S (fun l hl => Finset.mem_image.mpr ⟨l,hl,rfl⟩),?_⟩
  intro s hs
  apply badFaceProjection_raw_eq_zero G r s
  intro l hl he
  exact hs (Finset.mem_image.mpr ⟨l,hl,he⟩)

/-- Prefixing a vertex already in a simplex gives a repeated-vertex zero. -/
theorem cons_simplex_eq_zero_of_mem (a : V) (l : List V) (ha : a ∈ l) :
    cons a (simplex l) = 0 := by
  rw [cons_simplex]
  apply simplex_eq_zero_of_not_nodup
  intro h
  exact (List.nodup_cons.mp h).1 ha

/-- A projected component contains every vertex of its specified bad face. -/
theorem cons_badFaceProjection_eq_zero (G : V → Prop) (s : Finset V) (a : V) (ha : a ∈ s)
    (c : Chain V) : cons a (badFaceProjection G s c) = 0 := by
  have he : (cons a).comp (badFaceProjection G s) = (0 : Chain V →ₗ[ℚ] Chain V) := by
    apply chain_ext
    intro l
    change cons a (badFaceProjection G s (simplex l)) = 0
    classical
    by_cases hs : badVertices G l = s
    · rw [badFaceProjection_simplex,ite_eq_left hs]
      have hb : a ∈ badVertices G l := hs.symm ▸ ha
      have hh : a ∈ l ∧ ¬G a := by
        simpa only [badVertices,Finset.mem_filter,List.mem_toFinset] using hb
      have hal : a ∈ l := hh.1
      exact cons_simplex_eq_zero_of_mem a l hal
    · rw [badFaceProjection_simplex,ite_eq_right hs,map_zero]
  exact LinearMap.congr_fun he c

/-- The exact factorization of a bad-face summand by its ordered face and contracted residual. -/
theorem badFaceProjection_eq_join_extract (G : V → Prop) (B : List V) (hB : B.Nodup)
    (c : Chain V) :
    join (simplex B) (extract B (badFaceProjection G B.toFinset c)) =
      badFaceProjection G B.toFinset c := by
  classical
  apply join_extract B hB
  intro a ha
  exact cons_badFaceProjection_eq_zero G B.toFinset a (List.mem_toFinset.mpr ha) c

end TernaryPoly.OrientedBadFaceDecomposition
