module

public import TernaryPeriodPolynomials.Building.OrientedChain.ChainJoin
public import Mathlib.LinearAlgebra.BilinearMap

@[expose] public section


/-! Actual functorial relabeling of the finite oriented-list chain quotient.
No group-action laws or boundary compatibility are assumed. -/

noncomputable section
namespace TernaryPoly.OrientedChainMap

open OrientedListChains OrientedChainJoin
variable {V W U : Type*}

/-- Raw relabeling is the finite-support pushforward along List.map. -/
def rawMap (f : V → W) : Raw V →ₗ[ℚ] Raw W :=
  Finsupp.lmapDomain ℚ ℚ (List.map f)

@[simp] theorem rawMap_simplex (f : V → W) (l : List V) :
    rawMap f (rawSimplex l) = rawSimplex (l.map f) := by
  simp [rawMap, rawSimplex, Finsupp.lmapDomain_apply]

/-- Raw relabeling commutes with prefixing the corresponding image vertex. -/
theorem rawMap_rawCons (f : V → W) (a : V) (c : Raw V) :
    rawMap f (rawCons a c) = rawCons (f a) (rawMap f c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l q =>
    have hq : Finsupp.single l q = q • rawSimplex l := by simp [rawSimplex]
    simp only [hq, map_smul, rawCons_simplex, rawMap_simplex, List.map_cons]

/-- Every generating orientation relation and its closure is preserved by actual relabeling. -/
theorem rawMap_relation (f : V → W) {c : Raw V} (hc : c ∈ relations V) :
    rawMap f c ∈ relations W := by
  induction hc with
  | swap a b l =>
    simp only [map_add, rawMap_simplex, List.map_cons]
    exact Relation.swap (f a) (f b) (l.map f)
  | cons a hc ih =>
    rw [rawMap_rawCons]
    exact Relation.cons (f a) ih
  | zero => simpa only [map_zero] using (relations W).zero_mem
  | add hc hd ihc ihd => simpa only [map_add] using (relations W).add_mem ihc ihd
  | smul q hc ih => simpa only [map_smul] using (relations W).smul_mem q ih

/-- The genuine rational linear relabeling map on the alternating quotient. -/
def map (f : V → W) : Chain V →ₗ[ℚ] Chain W :=
  (relations V).mapQ (relations W) (rawMap f) (fun _ hc => rawMap_relation f hc)

@[simp] theorem map_simplex (f : V → W) (l : List V) :
    map f (simplex l) = simplex (l.map f) := by
  simp [map, simplex, Submodule.mapQ_apply, rawMap_simplex]

/-- Relabeling commutes with the actual cone operator. -/
theorem map_cons (f : V → W) (a : V) (c : Chain V) :
    map f (cons a c) = cons (f a) (map f c) := by
  have h : (map f).comp (cons a) = (cons (f a)).comp (map f) := by
    apply chain_ext
    intro l
    simp only [LinearMap.comp_apply, cons_simplex, map_simplex, List.map_cons]
  exact LinearMap.congr_fun h c

/-- Identity vertex relabeling is the identity linear chain map. -/
@[simp] theorem map_id : map (id : V → V) = LinearMap.id := by
  apply chain_ext
  intro l
  simp only [map_simplex, List.map_id, LinearMap.id_apply]

/-- Composition of actual vertex maps induces composition of actual chain maps. -/
theorem map_comp (f : V → W) (g : W → U) : (map g).comp (map f) = map (g ∘ f) := by
  apply chain_ext
  intro l
  simp only [LinearMap.comp_apply, map_simplex, List.map_map]

theorem map_comp_apply (f : V → W) (g : W → U) (c : Chain V) :
    map g (map f c) = map (g ∘ f) c := LinearMap.congr_fun (map_comp f g) c

/-- The actual alternating-deletion boundary commutes with arbitrary vertex relabeling. -/
theorem boundary_map (f : V → W) (c : Chain V) :
    boundary (map f c) = map f (boundary c) := by
  have h : boundary.comp (map f) = (map f).comp boundary := by
    apply chain_ext
    intro l
    simp only [LinearMap.comp_apply, map_simplex]
    induction l with
    | nil => simp only [List.map_nil, boundary_nil, map_zero]
    | cons a l ih =>
      rw [List.map_cons, boundary_cons, boundary_cons, map_sub, map_cons, map_simplex, ih]
  exact LinearMap.congr_fun h c

/-- A concrete finite-face image hypothesis, with no implicit injectivity requirement. -/
def MapsFaces (f : V → W) (C : PreAbstractSimplicialComplex V)
    (D : PreAbstractSimplicialComplex W) : Prop :=
  by classical exact ∀ s : Finset V, s ∈ C → s.image f ∈ D

/-- Empty augmented faces and genuine faces are preserved under the stated face-map condition. -/
theorem allowed_map (f : V → W) (C : PreAbstractSimplicialComplex V)
    (D : PreAbstractSimplicialComplex W) (hf : MapsFaces f C D)
    {l : List V} (hl : Allowed C l) : Allowed D (l.map f) := by
  classical
  rcases hl with rfl | hl
  · exact Or.inl rfl
  · apply Or.inr
    have he : (l.map f).toFinset = l.toFinset.image f := by
      ext w
      simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
    rw [he]
    exact hf l.toFinset hl

/-- An actual face map preserves every finite oriented simplex-chain submodule. -/
theorem map_mem_chains (f : V → W) (C : PreAbstractSimplicialComplex V)
    (D : PreAbstractSimplicialComplex W) (hf : MapsFaces f C D) (n : ℕ)
    {c : Chain V} (hc : c ∈ chains C n) : map f c ∈ chains D n := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l, hlen, hl, rfl⟩ := hc
    rw [map_simplex]
    simpa only [List.length_map, hlen] using
      simplex_mem_chains D (l.map f) (allowed_map f C D hf hl)
  | zero => simpa only [map_zero] using (chains D n).zero_mem
  | add c d hc hd ihc ihd => simpa only [map_add] using (chains D n).add_mem ihc ihd
  | smul q c hc ih => simpa only [map_smul] using (chains D n).smul_mem q ih

/-- The induced linear map between the actual n-vertex chain modules of two complexes. -/
def chainMap (f : V → W) (C : PreAbstractSimplicialComplex V)
    (D : PreAbstractSimplicialComplex W) (hf : MapsFaces f C D) (n : ℕ) :
    chains C n →ₗ[ℚ] chains D n :=
  ((map f).comp (chains C n).subtype).codRestrict _
    (fun c => map_mem_chains f C D hf n c.property)

/-- The restricted face maps commute with the genuine chain differentials. -/
theorem chainMap_differential (f : V → W) (C : PreAbstractSimplicialComplex V)
    (D : PreAbstractSimplicialComplex W) (hf : MapsFaces f C D) (n : ℕ)
    (c : chains C (n + 1)) :
    differential D n (chainMap f C D hf (n + 1) c) =
      chainMap f C D hf n (differential C n c) := by
  apply Subtype.ext
  exact boundary_map f c.val

/-- A genuine vertex equivalence induces a genuine rational linear chain equivalence. -/
def mapEquiv (e : V ≃ W) : Chain V ≃ₗ[ℚ] Chain W where
  __ := map e
  invFun := map e.symm
  left_inv c := by
    change map e.symm (map e c) = c
    rw [map_comp_apply]
    have he : (e.symm : W → V) ∘ (e : V → W) = id := by
      funext v
      exact e.symm_apply_apply v
    rw [he, map_id]
    rfl
  right_inv c := by
    change map e (map e.symm c) = c
    rw [map_comp_apply]
    have he : (e : V → W) ∘ (e.symm : W → V) = id := by
      funext w
      exact e.apply_symm_apply w
    rw [he, map_id]
    rfl

@[simp] theorem mapEquiv_apply (e : V ≃ W) (c : Chain V) : mapEquiv e c = map e c := rfl

/-- Relabeling preserves the actual bilinear join because it preserves list concatenation. -/
theorem map_join (f : V → W) (c d : Chain V) :
    map f (join c d) = join (map f c) (map f d) := by
  have h : (map f).comp (join.flip d) = (join.flip (map f d)).comp (map f) := by
    apply chain_ext
    intro l
    change map f (join (simplex l) d) = join (map f (simplex l)) (map f d)
    have h' : (map f).comp (join (simplex l)) =
        (join (map f (simplex l))).comp (map f) := by
      apply chain_ext
      intro m
      simp only [LinearMap.comp_apply, join_simplex, map_simplex, List.map_append]
    exact LinearMap.congr_fun h' d
  exact LinearMap.congr_fun h c

/-- A left inverse of vertex maps gives a left inverse of their actual chain maps. -/
theorem map_leftInverse (f : V → W) (g : W → V) (h : Function.LeftInverse g f) :
    Function.LeftInverse (map g) (map f) := by
  intro c
  rw [map_comp_apply]
  have he : g ∘ f = id := funext h
  rw [he,map_id]
  rfl

/-- Injective vertex relabeling is injective on the actual oriented-chain quotient. -/
theorem map_injective [Nonempty V] (f : V → W) (h : Function.Injective f) :
    Function.Injective (map f) :=
  (map_leftInverse f (Function.invFun f) (Function.leftInverse_invFun h)).injective

/-- An injective vertex relabeling detects zero chains. -/
theorem map_eq_zero_iff [Nonempty V] (f : V → W) (h : Function.Injective f) (c : Chain V) :
    map f c = 0 ↔ c = 0 := by
  constructor
  · intro hc
    exact map_injective f h (hc.trans (map_zero (map f)).symm)
  · intro hc
    rw [hc,map_zero]

end TernaryPoly.OrientedChainMap
