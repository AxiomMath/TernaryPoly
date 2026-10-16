module

public import TernaryPeriodPolynomials.Building.Good.RelativeChains
public import TernaryPeriodPolynomials.Building.Ambient.DependentTriangles
public import TernaryPeriodPolynomials.Building.OrientedChain.SimplexPermutation

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodRelativePresentationFrames
open ModThreeGoodAction GoodIntegralNormalization PrimitiveLineUniqueness
open AugmentedFrameComplex AugmentedBadFaces GoodAugmentedNormalForm
open IntegralFrameHeightReduction GoodRelativeChains ReferenceCoefficientMatrices
open OrientedListChains
local instance : DecidableEq RationalLine := Classical.decEq _

/-- Ordered column lines determine the actual residue-one integral frame uniquely. -/
theorem K_eq_of_column_lines (g h : K)
    (he : ∀ j : Fin 3, augmentedLine g.val j.castSucc = augmentedLine h.val j.castSucc) : g = h := by
  have hc (j : Fin 3) : g.val.val.col j = h.val.val.col j := by
    apply primitive_eq_of_residue_one_of_span_eq (column_primitive g.val j) (column_primitive h.val j)
    · exact columnResidue_K g j
    · exact columnResidue_K h j
    · rw [← columnLine_span,← columnLine_span,he j]
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact congrFun (hc j) i

/-- The literal ordered K-triangle parametrization has no stabilizer ambiguity. -/
theorem triangleList_injective : Function.Injective (fun g : K => triangleList g.val) := by
  intro g h he
  have hh : augmentedLine g.val 0 = augmentedLine h.val 0 ∧
      augmentedLine g.val 1 = augmentedLine h.val 1 ∧ augmentedLine g.val 2 = augmentedLine h.val 2 := by
    simpa only [triangleList,List.cons.injEq,and_true] using he
  apply K_eq_of_column_lines g h
  intro j
  fin_cases j
  · exact hh.1
  · exact hh.2.1
  · exact hh.2.2

/-- The reference cyclic matrix literally cycles the actual integer columns. -/
theorem mul_cK_column (g : K) (j : Fin 3) :
    (g*cK).val.val.col j = g.val.val.col ((![1,2,0] : Fin 3 → Fin 3) j) := by
  ext i
  change (∑ k : Fin 3, g.val.val i k * cMatrix k j) = g.val.val i ((![1,2,0] : Fin 3 → Fin 3) j)
  fin_cases j <;> simp [cMatrix,Fin.sum_univ_three]

/-- The reference transposition literally exchanges the first two integer columns. -/
theorem mul_sK_column (g : K) (j : Fin 3) :
    (g*sK).val.val.col j = g.val.val.col ((![1,0,2] : Fin 3 → Fin 3) j) := by
  ext i
  change (∑ k : Fin 3, g.val.val i k * sMatrix k j) = g.val.val i ((![1,0,2] : Fin 3 → Fin 3) j)
  fin_cases j <;> simp [sMatrix,Fin.sum_univ_three]

theorem mul_cK_line (g : K) (j : Fin 3) :
    augmentedLine (g*cK).val j.castSucc =
      augmentedLine g.val ((![1,2,0] : Fin 3 → Fin 3) j).castSucc := by
  apply Subtype.ext
  rw [columnLine_span,columnLine_span,mul_cK_column]

theorem mul_sK_line (g : K) (j : Fin 3) :
    augmentedLine (g*sK).val j.castSucc =
      augmentedLine g.val ((![1,0,2] : Fin 3 → Fin 3) j).castSucc := by
  apply Subtype.ext
  rw [columnLine_span,columnLine_span,mul_sK_column]

/-- The cyclic generator acts by the literal cyclic list permutation. -/
theorem triangleList_mul_cK (g : K) : triangleList (g*cK).val =
    [augmentedLine g.val 1,augmentedLine g.val 2,augmentedLine g.val 0] := by
  exact congrArg (fun v : Fin 3 → RationalLine => [v 0,v 1,v 2])
    (funext (mul_cK_line g))

/-- The swap generator acts by the literal first-two list transposition. -/
theorem triangleList_mul_sK (g : K) : triangleList (g*sK).val =
    [augmentedLine g.val 1,augmentedLine g.val 0,augmentedLine g.val 2] := by
  exact congrArg (fun v : Fin 3 → RationalLine => [v 0,v 1,v 2])
    (funext (mul_sK_line g))

/-- Every K-triangle has full rational span. -/
theorem triangleList_finrank_ge (g : K) :
    3 ≤ Module.finrank ℚ (faceSpan (triangleList g.val).toFinset) := by
  convert AmbientDependentTriangles.basis_face_finrank_ge g.val using 1
  apply congrArg (fun s : Finset RationalLine => Module.finrank ℚ (faceSpan s))
  ext L
  simp only [triangleList,List.mem_toFinset]

/-- A proper-span list cannot be a K-frame triangle. -/
theorem not_triangleList_of_proper (l : List RationalLine)
    (hd : Module.finrank ℚ (faceSpan l.toFinset) ≤ 2) : ¬∃ g : K, triangleList g.val = l := by
  rintro ⟨g,rfl⟩
  have hh := triangleList_finrank_ge g
  omega

/-- A nondegenerate four-vertex ambient face uses the entire augmented frame. -/
theorem four_face_eq_augmentedFrame (l : List RationalLine) (hlen : l.length = 4)
    (hn : l.Nodup) (hf : l.toFinset ∈ ambient) :
    ∃ g : ModThreeGoodAction.IntegralGL, l.toFinset = augmentedFrame g := by
  obtain ⟨_,g,hg⟩ := hf
  refine ⟨g,Finset.eq_of_subset_of_card_le hg ?_⟩
  rw [augmentedFrame_card,List.toFinset_card_of_nodup hn,hlen]

/-- Every actual nondegenerate Good tetrahedron is a K translate of the reference tetrahedron. -/
theorem good_tetrahedron_perm (l : List RationalLine) (hlen : l.length = 4)
    (hn : l.Nodup) (hf : l.toFinset ∈ good) :
    ∃ g : K, l.Perm (tetrahedronList g.val) := by
  classical
  obtain ⟨a,ha⟩ := four_face_eq_augmentedFrame l hlen hn hf.1
  obtain ⟨g,hg⟩ := exists_K_augmentedFrame a (by
    intro L hL
    exact hf.2 L (ha.symm ▸ hL))
  refine ⟨g,List.perm_of_nodup_nodup_toFinset_eq hn ?_ ?_⟩
  · have hn' : ([0,1,3,2] : List (Fin 4)).Nodup := by decide
    exact hn'.map (augmentedLine_injective g.val)
  · rw [ha,hg]
    ext L
    simp only [augmentedFrame,Finset.mem_image,Finset.mem_univ,true_and,
      tetrahedronList,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨3,rfl⟩
      · exact ⟨2,rfl⟩

/-- Explicit list-level cyclic transport for any displayed K-frame ordering. -/
theorem triangleList_cycle_of_eq (g : K) (L M N : RationalLine)
    (hg : triangleList g.val = [L,M,N]) : triangleList (g*cK).val = [M,N,L] := by
  have he : augmentedLine g.val 0 = L ∧ augmentedLine g.val 1 = M ∧ augmentedLine g.val 2 = N := by
    simpa only [triangleList,List.cons.injEq,and_true] using hg
  rw [triangleList_mul_cK,he.1,he.2.1,he.2.2]

/-- Explicit list-level transposition transport for any displayed K-frame ordering. -/
theorem triangleList_swap_of_eq (g : K) (L M N : RationalLine)
    (hg : triangleList g.val = [L,M,N]) : triangleList (g*sK).val = [M,L,N] := by
  have he : augmentedLine g.val 0 = L ∧ augmentedLine g.val 1 = M ∧ augmentedLine g.val 2 = N := by
    simpa only [triangleList,List.cons.injEq,and_true] using hg
  rw [triangleList_mul_sK,he.1,he.2.1,he.2.2]

/-- Every actual Good triangle is proper or is the literal ordered triangle of a K-frame. -/
theorem good_triangle_cases (l : List RationalLine) (hlen : l.length = 3)
    (hl : Allowed good l) : l.toFinset ∈ properGood ∨ ∃ g : K, triangleList g.val = l := by
  classical
  obtain ⟨L,M,N,rfl⟩ := List.length_eq_three.mp hlen
  have hg : [L,M,N].toFinset ∈ good := by
    rcases hl with he | hl
    · simp at he
    · exact hl
  by_cases hd : Module.finrank ℚ (faceSpan [L,M,N].toFinset) ≤ 2
  · exact Or.inl ⟨hg,hd⟩
  · right
    have hle : Module.finrank ℚ (faceSpan [L,M,N].toFinset) ≤ 3 := by
      simpa only [Space,Module.finrank_pi,Module.finrank_self,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using
        Submodule.finrank_le (faceSpan [L,M,N].toFinset)
    have he : Module.finrank ℚ (faceSpan [L,M,N].toFinset) = 3 := by omega
    have hi : Finset.univ.image (![L,M,N] : Fin 3 → RationalLine) = [L,M,N].toFinset := by
      ext x
      simp [Fin.exists_fin_succ,eq_comm]
    obtain ⟨g,hgL⟩ := exists_K_triangle ![L,M,N] (by rwa [hi]) (by rwa [hi])
    refine ⟨g,?_⟩
    have h0 : augmentedLine g.val 0 = L := hgL 0
    have h1 : augmentedLine g.val 1 = M := hgL 1
    have h2 : augmentedLine g.val 2 = N := hgL 2
    simp only [triangleList,h0,h1,h2]

end TernaryPoly.GoodRelativePresentationFrames
