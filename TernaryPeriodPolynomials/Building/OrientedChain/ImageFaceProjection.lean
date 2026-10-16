module

public import TernaryPeriodPolynomials.Building.OrientedChain.ChainProjection
public import TernaryPeriodPolynomials.Building.OrientedChain.BadFaceDecomposition
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainMap

@[expose] public section


noncomputable section
namespace TernaryPoly.OrientedImageFaceProjection
open OrientedListChains OrientedChainJoin OrientedChainProjection OrientedBadFaceDecomposition
variable {V W : Type*}
local instance : DecidableEq W := Classical.decEq W

/-- The exact finite image face of a displayed simplex under a vertex map. -/
def imageFace (f : V → W) (l : List V) : Finset W := (l.map f).toFinset

theorem imageFace_perm (f : V → W) {l m : List V} (h : l.Perm m) :
    imageFace f l = imageFace f m := by
  ext w
  simp only [imageFace,List.mem_toFinset,(h.map f).mem_iff]

/-- Retain precisely the simplices with the specified image face. -/
def project (f : V → W) (s : Finset W) : Chain V →ₗ[ℚ] Chain V :=
  filter (fun l => imageFace f l = s) (fun h => by dsimp only; rw [imageFace_perm f h])

@[simp] theorem project_simplex (f : V → W) (s : Finset W) (l : List V) :
    project f s (simplex l) = if imageFace f l = s then simplex l else 0 := by
  classical
  have he := filter_simplex (fun l => imageFace f l = s)
    (fun h => by dsimp only; rw [imageFace_perm f h]) l
  convert he using 1
  · rfl
  · split_ifs <;> rfl

theorem project_mem_chains (f : V → W) (s : Finset W)
    (C : PreAbstractSimplicialComplex V) (n : ℕ) {c : Chain V} (hc : c ∈ chains C n) :
    project f s c ∈ chains C n :=
  filter_mem_chains (fun l => imageFace f l = s) (fun h => by dsimp only; rw [imageFace_perm f h]) C n hc

theorem project_idempotent (f : V → W) (s : Finset W) (c : Chain V) :
    project f s (project f s c) = project f s c :=
  filter_idempotent (fun l => imageFace f l = s) (fun h => by dsimp only; rw [imageFace_perm f h]) c

theorem project_orthogonal (f : V → W) (s t : Finset W) (hst : s ≠ t) (c : Chain V) :
    project f s (project f t c) = 0 := by
  have he : (project f s).comp (project f t) = (0 : Chain V →ₗ[ℚ] Chain V) := by
    apply chain_ext
    intro l
    by_cases ht : imageFace f l = t <;> simp [ht,Ne.symm hst]
  exact LinearMap.congr_fun he c

/-- Relabeling preserves exact image-face components, including degenerate projected simplices. -/
theorem map_project (f : V → W) (s : Finset W) (c : Chain V) :
    OrientedChainMap.map f (project f s c) =
      project (id : W → W) s (OrientedChainMap.map f c) := by
  have he : (OrientedChainMap.map f).comp (project f s) =
      (project (id : W → W) s).comp (OrientedChainMap.map f) := by
    apply chain_ext
    intro l
    change OrientedChainMap.map f (project f s (simplex l)) =
      project id s (OrientedChainMap.map f (simplex l))
    have hid : imageFace (id : W → W) (l.map f) = imageFace f l := by simp [imageFace]
    rw [project_simplex,OrientedChainMap.map_simplex,project_simplex,hid]
    by_cases hs : imageFace f l = s <;>
      simp only [hs,ite_true,ite_false,OrientedChainMap.map_simplex,map_zero]
  exact LinearMap.congr_fun he c

/-- Zero total projected chain forces every projected-face component to map to zero separately. -/
theorem map_project_eq_zero (f : V → W) (s : Finset W) {c : Chain V}
    (hc : OrientedChainMap.map f c = 0) : OrientedChainMap.map f (project f s c) = 0 := by
  rw [map_project,hc,map_zero]

theorem sum_project_raw (f : V → W) (r : Raw V) (S : Finset (Finset W))
    (hS : ∀ l ∈ r.support, imageFace f l ∈ S) :
    ∑ s ∈ S, project f s ((relations V).mkQ r) = (relations V).mkQ r := by
  classical
  rw [mkQ_expansion]
  simp only [map_sum,map_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← Finset.smul_sum]
  congr 1
  simp [hS l hl]

theorem project_raw_eq_zero (f : V → W) (r : Raw V) (s : Finset W)
    (hs : ∀ l ∈ r.support, imageFace f l ≠ s) : project f s ((relations V).mkQ r) = 0 := by
  classical
  rw [mkQ_expansion]
  simp only [map_sum,map_smul]
  apply Finset.sum_eq_zero
  intro l hl
  simp only [project_simplex,hs l hl,ite_false,smul_zero]

/-- An actual finite chain has a finite exact decomposition by its projected base faces. -/
theorem exists_decomposition (f : V → W) (c : Chain V) :
    ∃ S : Finset (Finset W), (∑ s ∈ S, project f s c) = c ∧
      ∀ s ∉ S, project f s c = 0 := by
  classical
  refine Quotient.inductionOn' c (fun r => ?_)
  let S := r.support.image (imageFace f)
  refine ⟨S,sum_project_raw f r S (fun l hl => Finset.mem_image.mpr ⟨l,hl,rfl⟩),?_⟩
  intro s hs
  apply project_raw_eq_zero f r s
  intro l hl he
  exact hs (Finset.mem_image.mpr ⟨l,hl,he⟩)

end TernaryPoly.OrientedImageFaceProjection
