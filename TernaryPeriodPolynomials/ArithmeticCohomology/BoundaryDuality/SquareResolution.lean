module

public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Basic

@[expose] public section


/-!
# The square resolution of `ℂ` over `ℤ²`

The plane `ℝ²` is tiled by unit squares with vertices in `ℤ²`. Its augmented cellular chain
complex, with complex coefficients and with the lattice `ℤ²` acting by translation, is a free
resolution of `ℂ` of length two by permutation modules: index `0` is the augmentation point,
index `1` carries the vertices `ℤ²`, index `2` carries the edges `ℤ² × Fin 2` (an edge is
determined by its initial vertex and its direction, horizontal or vertical), index `3` carries the
squares `ℤ²` (a square is determined by its lower left corner), and there are no cells beyond.

The boundary of an edge is its terminal vertex minus its initial vertex, and the boundary of a
square is the horizontal edge below it, plus the vertical edge to its right, minus the horizontal
edge above it, minus the vertical edge to its left. Translations act freely on the cells.

Exactness is proved by reduction modulo boundaries. Every vertex is congruent to the origin modulo
edge boundaries, which gives exactness at the vertices. Every edge is congruent, modulo square
boundaries, to a chain on the comb consisting of all vertical edges and of the horizontal edges on
the axis; a one-cycle supported on the comb vanishes by an extremal argument on its vertical edges
followed by one on its horizontal edges. Finally, a two-chain with vanishing boundary is zero by an
extremal argument on its support.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.SquareResolution

open TernaryPeriodPolynomials.TopVanishing
open Finsupp (single)

/-- The group of lattice translations of the square tiling, written multiplicatively. -/
abbrev SqGroup : Type := Multiplicative (ℤ × ℤ)

/-- Finitely supported complex chains on the vertices `ℤ²`. -/
abbrev VertChain : Type := (ℤ × ℤ) →₀ ℂ

/-- Finitely supported complex chains on the edges `ℤ² × Fin 2`. -/
abbrev EdgeChain : Type := ((ℤ × ℤ) × Fin 2) →₀ ℂ

/-- The basis chain of the vertex `(x, y)`. -/
abbrev vt (x y : ℤ) : VertChain := single (x, y) 1

/-- The basis chain of the horizontal edge from `(x, y)` to `(x + 1, y)`. -/
abbrev hE (x y : ℤ) : EdgeChain := single ((x, y), 0) 1

/-- The basis chain of the vertical edge from `(x, y)` to `(x, y + 1)`. -/
abbrev vE (x y : ℤ) : EdgeChain := single ((x, y), 1) 1

/-! ### The translation action on the cells -/

/-- Translation of vertices (and of squares, labelled by their lower left corner). -/
instance (priority := high) vertexAction : MulAction SqGroup (ℤ × ℤ) where
  smul γ p := Multiplicative.toAdd γ + p
  one_smul p := by
    change Multiplicative.toAdd (1 : SqGroup) + p = p
    simp
  mul_smul γ δ p := by
    change Multiplicative.toAdd (γ * δ) + p = Multiplicative.toAdd γ + (Multiplicative.toAdd δ + p)
    simp [add_assoc]

/-- Translation of edges: the initial vertex moves and the direction is kept. -/
instance (priority := high) edgeAction : MulAction SqGroup ((ℤ × ℤ) × Fin 2) where
  smul γ e := (Multiplicative.toAdd γ + e.1, e.2)
  one_smul e := by
    change (Multiplicative.toAdd (1 : SqGroup) + e.1, e.2) = e
    simp
  mul_smul γ δ e := by
    change (Multiplicative.toAdd (γ * δ) + e.1, e.2) =
      (Multiplicative.toAdd γ + (Multiplicative.toAdd δ + e.1), e.2)
    simp [add_assoc]

/-- The trivial action on the augmentation point. -/
instance (priority := high) pointAction : MulAction SqGroup Unit where
  smul _ u := u
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The (vacuous) action on an empty type of cells. -/
instance (priority := high) emptyAction : MulAction SqGroup Empty where
  smul _ e := e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- A translation moves a vertex by its translation vector. -/
theorem vertex_smul (γ : SqGroup) (p : ℤ × ℤ) : γ • p = Multiplicative.toAdd γ + p := rfl

/-- A translation moves the initial vertex of an edge by its translation vector. -/
theorem edge_smul (γ : SqGroup) (p : ℤ × ℤ) (i : Fin 2) :
    γ • (p, i) = (Multiplicative.toAdd γ + p, i) := rfl

/-- A translation fixes the augmentation point. -/
theorem unit_smul (γ : SqGroup) (u : Unit) : γ • u = u := rfl

/-- A translation vector that is zero is the identity of the group. -/
theorem eq_one_of_toAdd_eq_zero {γ : SqGroup} (h : Multiplicative.toAdd γ = 0) : γ = 1 :=
  h

/-- Translations act freely on vertices. -/
theorem vertex_free (γ : SqGroup) (p : ℤ × ℤ) (h : γ • p = p) : γ = 1 := by
  have h' : Multiplicative.toAdd γ + p = p := h
  exact eq_one_of_toAdd_eq_zero (by simpa using h')

/-- Translations act freely on edges. -/
theorem edge_free (γ : SqGroup) (e : (ℤ × ℤ) × Fin 2) (h : γ • e = e) : γ = 1 := by
  have h' : Multiplicative.toAdd γ + e.1 = e.1 := congrArg Prod.fst h
  exact eq_one_of_toAdd_eq_zero (by simpa using h')

/-! ### Auxiliary facts -/

/-- The index of an edge direction is zero or one. -/
theorem fin_two_cases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide

/-- Induction on the integers, in the form of closure under `n ↦ n + 1` and `n ↦ n - 1`. -/
theorem int_induction {S : ℤ → Prop} (h0 : S 0) (hup : ∀ n, S n → S (n + 1))
    (hdown : ∀ n, S n → S (n - 1)) : ∀ n, S n := by
  intro n
  refine Int.induction_on n h0 ?_ ?_
  · intro i ih
    exact hup _ ih
  · intro i ih
    exact hdown _ ih

/-- The unit step in the horizontal (direction `0`) or vertical (direction `1`) direction. -/
def step (i : Fin 2) : ℤ × ℤ := if i = 0 then (1, 0) else (0, 1)

/-- The horizontal unit step. -/
@[simp] theorem step_zero : step 0 = (1, 0) := rfl

/-- The vertical unit step. -/
@[simp] theorem step_one : step 1 = (0, 1) := rfl

/-! ### The boundary maps -/

/-- The augmentation: every vertex goes to the point. -/
def d0 : VertChain →ₗ[ℂ] (Unit →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun _ => single () (1 : ℂ))

/-- The boundary of an edge: its terminal vertex minus its initial vertex. -/
def d1 : EdgeChain →ₗ[ℂ] VertChain :=
  Finsupp.linearCombination ℂ (fun e : (ℤ × ℤ) × Fin 2 =>
    single (e.1 + step e.2) (1 : ℂ) - single e.1 (1 : ℂ))

/-- The boundary of the square with lower left corner `p`: the lower edge, plus the right edge,
minus the upper edge, minus the left edge. -/
def d2 : VertChain →ₗ[ℂ] EdgeChain :=
  Finsupp.linearCombination ℂ (fun p : ℤ × ℤ =>
    single (p, (0 : Fin 2)) (1 : ℂ) + single (p + (1, 0), (1 : Fin 2)) (1 : ℂ) -
      single (p + (0, 1), (0 : Fin 2)) (1 : ℂ) - single (p, (1 : Fin 2)) (1 : ℂ))

/-- The augmentation on a basis chain. -/
theorem d0_single (p : ℤ × ℤ) (a : ℂ) : d0 (single p a) = single () a := by
  simp [d0]

/-- The boundary of an edge chain on a basis chain. -/
theorem d1_single (e : (ℤ × ℤ) × Fin 2) (a : ℂ) :
    d1 (single e a) = single (e.1 + step e.2) a - single e.1 a := by
  simp only [d1, Finsupp.linearCombination_single, smul_sub, Finsupp.smul_single, smul_eq_mul,
    mul_one]

/-- The boundary of a square chain on a basis chain. -/
theorem d2_single (p : ℤ × ℤ) (a : ℂ) :
    d2 (single p a) = single (p, (0 : Fin 2)) a + single (p + (1, 0), (1 : Fin 2)) a -
      single (p + (0, 1), (0 : Fin 2)) a - single (p, (1 : Fin 2)) a := by
  simp only [d2, Finsupp.linearCombination_single, smul_add, smul_sub, Finsupp.smul_single,
    smul_eq_mul, mul_one]

/-- The boundary of a horizontal edge. -/
theorem d1_hE (x y : ℤ) : d1 (hE x y) = vt (x + 1) y - vt x y := by
  simp only [hE, vt, d1_single, step_zero, Prod.mk_add_mk, add_zero]

/-- The boundary of a vertical edge. -/
theorem d1_vE (x y : ℤ) : d1 (vE x y) = vt x (y + 1) - vt x y := by
  simp only [vE, vt, d1_single, step_one, Prod.mk_add_mk, add_zero]

/-- The boundary of a square. -/
theorem d2_vt (x y : ℤ) :
    d2 (vt x y) = hE x y + vE (x + 1) y - hE x (y + 1) - vE x y := by
  simp only [hE, vE, vt, d2_single, Prod.mk_add_mk, add_zero]

/-- The two corners reached from a vertex by one horizontal and one vertical step agree. -/
theorem corner (p : ℤ × ℤ) : p + (1, 0) + (0, 1) = p + (0, 1) + (1, 0) :=
  add_right_comm _ _ _

/-- The boundary of a boundary of squares vanishes in the edges. -/
theorem d1_comp_d2 : d1 ∘ₗ d2 = 0 := by
  apply Finsupp.lhom_ext
  intro p a
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, d2_single, map_add, map_sub, d1_single,
    step_zero, step_one, corner]
  abel

/-- The augmentation kills edge boundaries. -/
theorem d0_comp_d1 : d0 ∘ₗ d1 = 0 := by
  apply Finsupp.lhom_ext
  intro e a
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, d1_single, map_sub, d0_single, sub_self]

/-! ### Equivariance -/

/-- The augmentation is equivariant. -/
theorem d0_equivariant : Equivariant SqGroup d0 := by
  apply equivariant_of_single
  intro γ p
  simp only [d0_single, chainAct_single, unit_smul]

/-- The edge boundary is equivariant. -/
theorem d1_equivariant : Equivariant SqGroup d1 := by
  apply equivariant_of_single
  rintro γ ⟨p, i⟩
  simp only [edge_smul, vertex_smul, d1_single, map_sub, chainAct_single, add_assoc]

/-- The square boundary is equivariant. -/
theorem d2_equivariant : Equivariant SqGroup d2 := by
  apply equivariant_of_single
  intro γ p
  simp only [vertex_smul, d2_single, map_add, map_sub, chainAct_single, edge_smul, add_assoc]

/-! ### The complex -/

/-- The cells of the square tiling: the augmentation point, the vertices, the edges, the squares,
and nothing beyond. -/
def squareCell : ℕ → Type
  | 0 => Unit
  | 1 => ℤ × ℤ
  | 2 => (ℤ × ℤ) × Fin 2
  | 3 => ℤ × ℤ
  | _ + 4 => Empty

/-- The translation action on the cells of each index. -/
instance squareCellAction : ∀ k, MulAction SqGroup (squareCell k)
  | 0 => pointAction
  | 1 => vertexAction
  | 2 => edgeAction
  | 3 => vertexAction
  | _ + 4 => emptyAction

/-- The boundary from index `k + 1` to index `k`. -/
def squareBoundary : ∀ k, (squareCell (k + 1) →₀ ℂ) →ₗ[ℂ] (squareCell k →₀ ℂ)
  | 0 => d0
  | 1 => d1
  | 2 => d2
  | _ + 3 => 0

/-- Every boundary of the square complex is equivariant. -/
theorem squareBoundary_equivariant (k : ℕ) : Equivariant SqGroup (squareBoundary k) := by
  rcases k with _ | _ | _ | k
  · exact d0_equivariant
  · exact d1_equivariant
  · exact d2_equivariant
  · exact equivariant_zero

/-- The boundary of a boundary vanishes in the square complex. -/
theorem squareBoundary_comp (k : ℕ) : squareBoundary k ∘ₗ squareBoundary (k + 1) = 0 := by
  rcases k with _ | _ | _ | k
  · exact d0_comp_d1
  · exact d1_comp_d2
  · exact LinearMap.comp_zero _
  · exact LinearMap.zero_comp _

/-- The square complex as a complex of permutation modules. -/
def squareComplex : PermutationComplex SqGroup where
  cell := squareCell
  action := squareCellAction
  d := squareBoundary
  equivariant := squareBoundary_equivariant
  d_comp_d := squareBoundary_comp

/-- Translations act freely on the cells of positive index. -/
theorem squareComplex_free : squareComplex.Free := by
  intro k γ s h
  rcases k with _ | _ | _ | k
  · exact vertex_free γ s h
  · exact edge_free γ s h
  · exact vertex_free γ s h
  · exact Empty.elim (s : Empty)

/-! ### Coefficient formulas -/

/-- The coefficient of the vertex `(x, y)` in the boundary of an edge chain. -/
theorem d1_apply (z : EdgeChain) (x y : ℤ) :
    d1 z (x, y) = z ((x - 1, y), 0) - z ((x, y), 0) + z ((x, y - 1), 1) - z ((x, y), 1) := by
  refine Finsupp.induction_linear z ?_ ?_ ?_
  · simp
  · intro f g hf hg
    simp only [map_add, Finsupp.add_apply, hf, hg]
    ring
  · rintro ⟨⟨u, w⟩, i⟩ a
    rcases fin_two_cases i with rfl | rfl
    · simp [d1_single, Finsupp.single_apply]
      all_goals (try split_ifs)
      all_goals
        first
          | (exfalso; omega)
          | ring1
    · simp [d1_single, Finsupp.single_apply]
      all_goals (try split_ifs)
      all_goals
        first
          | (exfalso; omega)
          | ring1

/-- A cycle has vanishing coefficient at every vertex. -/
theorem d1_cycle {z : EdgeChain} (h : d1 z = 0) (x y : ℤ) :
    z ((x - 1, y), 0) - z ((x, y), 0) + z ((x, y - 1), 1) - z ((x, y), 1) = 0 := by
  have h1 := d1_apply z x y
  rw [h] at h1
  simpa using h1.symm

/-- The coefficient of the horizontal edge `(x, y)` in the boundary of a square chain. -/
theorem d2_apply_h (c : VertChain) (x y : ℤ) :
    d2 c ((x, y), 0) = c (x, y) - c (x, y - 1) := by
  refine Finsupp.induction_linear c ?_ ?_ ?_
  · simp
  · intro f g hf hg
    simp only [map_add, Finsupp.add_apply, hf, hg]
    ring
  · rintro ⟨u, w⟩ a
    simp [d2_single, Finsupp.single_apply]
    all_goals (try split_ifs)
    all_goals
      first
        | (exfalso; omega)
        | ring1

/-! ### Injectivity of the square boundary -/

/-- A two-chain with vanishing boundary is zero: take a square of the support with the largest
height and look at the horizontal edge above it. -/
theorem d2_eq_zero (c : VertChain) (h : d2 c = 0) : c = 0 := by
  by_contra hne
  obtain ⟨⟨x, y⟩, hp, hmax⟩ := Finset.exists_max_image c.support (fun p => p.2)
    (Finsupp.support_nonempty_iff.mpr hne)
  have hcp : c (x, y) ≠ 0 := Finsupp.mem_support_iff.mp hp
  have hq : c (x, y + 1) = 0 := by
    by_contra hq
    have h' : y + 1 ≤ y := hmax (x, y + 1) (Finsupp.mem_support_iff.mpr hq)
    omega
  have hcoef := d2_apply_h c x (y + 1)
  have e : y + 1 - 1 = y := by omega
  rw [h, hq, e] at hcoef
  exact hcp (by simpa using hcoef)

/-! ### Exactness at the augmentation and at the vertices -/

/-- The linear functional giving the total coefficient of a vertex chain. -/
def eps : VertChain →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ (fun _ => (1 : ℂ))

/-- The total coefficient of a basis chain. -/
theorem eps_single (p : ℤ × ℤ) (a : ℂ) : eps (single p a) = a := by
  simp [eps]

/-- The augmentation is the total coefficient times the point. -/
theorem d0_apply (v : VertChain) : d0 v = eps v • single () (1 : ℂ) := by
  refine Finsupp.induction_linear v ?_ ?_ ?_
  · simp
  · intro f g hf hg
    rw [map_add, map_add, hf, hg, add_smul]
  · intro p a
    rw [d0_single, eps_single, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The augmentation is onto. -/
theorem range_d0 : LinearMap.range d0 = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro w
  refine ⟨single (0, 0) (w ()), ?_⟩
  rw [d0_single]
  refine Finsupp.ext fun u => ?_
  cases u
  simp

/-- Horizontal neighbours differ by an edge boundary. -/
theorem vt_step_x (x y : ℤ) : vt (x + 1) y - vt x y ∈ LinearMap.range d1 :=
  LinearMap.mem_range.mpr ⟨hE x y, d1_hE x y⟩

/-- Vertical neighbours differ by an edge boundary. -/
theorem vt_step_y (x y : ℤ) : vt x (y + 1) - vt x y ∈ LinearMap.range d1 :=
  LinearMap.mem_range.mpr ⟨vE x y, d1_vE x y⟩

/-- Every vertex is congruent to the one on the axis above or below it. -/
theorem vt_y (x : ℤ) : ∀ y : ℤ, vt x y - vt x 0 ∈ LinearMap.range d1 := by
  apply int_induction
  · simp
  · intro y h
    have e : vt x (y + 1) - vt x 0 = (vt x (y + 1) - vt x y) + (vt x y - vt x 0) := by abel
    rw [e]
    exact add_mem (vt_step_y x y) h
  · intro y h
    have h2 := vt_step_y x (y - 1)
    rw [sub_add_cancel] at h2
    have e : vt x (y - 1) - vt x 0 = (vt x y - vt x 0) - (vt x y - vt x (y - 1)) := by abel
    rw [e]
    exact sub_mem h h2

/-- Every vertex of the axis is congruent to the origin. -/
theorem vt_x : ∀ x : ℤ, vt x 0 - vt 0 0 ∈ LinearMap.range d1 := by
  apply int_induction
  · simp
  · intro x h
    have e : vt (x + 1) 0 - vt 0 0 = (vt (x + 1) 0 - vt x 0) + (vt x 0 - vt 0 0) := by abel
    rw [e]
    exact add_mem (vt_step_x x 0) h
  · intro x h
    have h2 := vt_step_x (x - 1) 0
    rw [sub_add_cancel] at h2
    have e : vt (x - 1) 0 - vt 0 0 = (vt x 0 - vt 0 0) - (vt x 0 - vt (x - 1) 0) := by abel
    rw [e]
    exact sub_mem h h2

/-- Every vertex is congruent to the origin modulo edge boundaries. -/
theorem vt_all (x y : ℤ) : vt x y - vt 0 0 ∈ LinearMap.range d1 := by
  have e : vt x y - vt 0 0 = (vt x y - vt x 0) + (vt x 0 - vt 0 0) := by abel
  rw [e]
  exact add_mem (vt_y x y) (vt_x x)

/-- A vertex chain differs from its total coefficient times the origin by an edge boundary. -/
theorem vertex_reduce (v : VertChain) : v - eps v • vt 0 0 ∈ LinearMap.range d1 := by
  refine Finsupp.induction_linear v ?_ ?_ ?_
  · simp
  · intro f g hf hg
    have e : f + g - eps (f + g) • vt 0 0 = (f - eps f • vt 0 0) + (g - eps g • vt 0 0) := by
      rw [map_add, add_smul]
      abel
    rw [e]
    exact add_mem hf hg
  · rintro ⟨x, y⟩ a
    have e : single (x, y) a - eps (single (x, y) a) • vt 0 0 = a • (vt x y - vt 0 0) := by
      rw [eps_single, smul_sub]
      simp
    rw [e]
    exact Submodule.smul_mem _ a (vt_all x y)

/-- Every vertex chain with total coefficient zero is an edge boundary. -/
theorem ker_d0_le : LinearMap.ker d0 ≤ LinearMap.range d1 := by
  intro v hv
  have h0 : d0 v = 0 := LinearMap.mem_ker.mp hv
  have h1 : eps v = 0 := by
    have h := congrArg (fun w : Unit →₀ ℂ => w ()) h0
    simpa [d0_apply] using h
  have h2 := vertex_reduce v
  rwa [h1, zero_smul, sub_zero] at h2

/-! ### Exactness at the edges -/

/-- The comb: all vertical edges and the horizontal edges on the axis `y = 0`. -/
def comb : Set ((ℤ × ℤ) × Fin 2) := {e | e.2 = 1 ∨ e.1.2 = 0}

/-- A basis chain on a comb edge is a chain supported on the comb. -/
theorem single_mem_comb_supported (e : (ℤ × ℤ) × Fin 2) (he : e ∈ comb) (a : ℂ) :
    single e a ∈ Finsupp.supported ℂ ℂ comb := by
  rw [Finsupp.mem_supported']
  intro f hf
  rw [Finsupp.single_apply, ite_eq_right]
  rintro rfl
  exact hf he

/-- Edge chains that are a sum of a square boundary and a chain on the comb. -/
abbrev Nsp : Submodule ℂ EdgeChain := LinearMap.range d2 ⊔ Finsupp.supported ℂ ℂ comb

/-- Vertical edges lie in the comb. -/
theorem vE_mem (x y : ℤ) : vE x y ∈ Nsp :=
  Submodule.mem_sup_right (single_mem_comb_supported _ (by simp [comb]) 1)

/-- The boundary of a square, as an element of the range of the square boundary. -/
theorem sq_mem (x y : ℤ) :
    hE x y + vE (x + 1) y - hE x (y + 1) - vE x y ∈ LinearMap.range d2 :=
  LinearMap.mem_range.mpr ⟨vt x y, d2_vt x y⟩

/-- The boundary of the square below the row `y`. -/
theorem sq_mem_pred (x y : ℤ) :
    hE x (y - 1) + vE (x + 1) (y - 1) - hE x y - vE x (y - 1) ∈ LinearMap.range d2 := by
  have h := sq_mem x (y - 1)
  rwa [sub_add_cancel] at h

/-- Every horizontal edge is congruent modulo square boundaries to a chain on the comb. -/
theorem hE_mem (x : ℤ) : ∀ y : ℤ, hE x y ∈ Nsp := by
  apply int_induction
  · exact Submodule.mem_sup_right (single_mem_comb_supported _ (by simp [comb]) 1)
  · intro y ih
    have e : hE x (y + 1) = (hE x y + vE (x + 1) y - vE x y) -
        (hE x y + vE (x + 1) y - hE x (y + 1) - vE x y) := by abel
    rw [e]
    exact sub_mem (sub_mem (add_mem ih (vE_mem _ _)) (vE_mem _ _))
      (Submodule.mem_sup_left (sq_mem x y))
  · intro y ih
    have hsq := sq_mem_pred x y
    have e : hE x (y - 1) = (hE x y - vE (x + 1) (y - 1) + vE x (y - 1)) +
        (hE x (y - 1) + vE (x + 1) (y - 1) - hE x y - vE x (y - 1)) := by abel
    rw [e]
    exact add_mem (add_mem (sub_mem ih (vE_mem _ _)) (vE_mem _ _))
      (Submodule.mem_sup_left hsq)

/-- Every edge chain is a sum of a square boundary and a chain on the comb. -/
theorem mem_Nsp (v : EdgeChain) : v ∈ Nsp := by
  refine Finsupp.induction_linear v ?_ ?_ ?_
  · exact zero_mem _
  · intro f g hf hg
    exact add_mem hf hg
  · rintro ⟨⟨x, y⟩, i⟩ a
    have e : single ((x, y), i) a = a • single ((x, y), i) (1 : ℂ) := by simp
    rw [e]
    refine Submodule.smul_mem _ a ?_
    rcases fin_two_cases i with rfl | rfl
    · exact hE_mem x y
    · exact vE_mem x y

/-- A one-cycle with no vertical edges vanishes: look at the horizontal edge with the largest
abscissa. -/
theorem horizontal_zero (z : EdgeChain) (hv : ∀ p, z (p, 1) = 0) (h : d1 z = 0) : z = 0 := by
  by_contra hne
  obtain ⟨⟨⟨x, y⟩, i⟩, he, hmax⟩ := Finset.exists_max_image z.support (fun e => e.1.1)
    (Finsupp.support_nonempty_iff.mpr hne)
  have hz : z ((x, y), i) ≠ 0 := Finsupp.mem_support_iff.mp he
  have hi : i = 0 := by
    rcases fin_two_cases i with h0 | h1
    · exact h0
    · exfalso
      apply hz
      rw [h1]
      exact hv (x, y)
  subst hi
  have hnext : z ((x + 1, y), 0) = 0 := by
    by_contra hne'
    have h' : x + 1 ≤ x := hmax ((x + 1, y), 0) (Finsupp.mem_support_iff.mpr hne')
    omega
  have hcyc := d1_cycle h (x + 1) y
  have e : x + 1 - 1 = x := by omega
  rw [e, hnext, hv, hv] at hcyc
  exact hz (by simpa using hcyc)

/-- A one-cycle supported on the comb has no vertical edges: look at the vertical edges of the
support with the largest and the smallest height. -/
theorem no_vertical (z : EdgeChain) (hz : ∀ x y : ℤ, y ≠ 0 → z ((x, y), 0) = 0)
    (h : d1 z = 0) : ∀ p, z (p, 1) = 0 := by
  by_contra hex
  obtain ⟨p, hp⟩ := not_forall.mp hex
  have hne : (z.support.filter (fun e => e.2 = 1)).Nonempty :=
    ⟨(p, 1), Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hp, rfl⟩⟩
  obtain ⟨⟨⟨x0, y0⟩, i0⟩, hmem0, hmax⟩ :=
    Finset.exists_max_image (z.support.filter (fun e => e.2 = 1)) (fun e => e.1.2) hne
  obtain ⟨⟨⟨x1, y1⟩, i1⟩, hmem1, hmin⟩ :=
    Finset.exists_min_image (z.support.filter (fun e => e.2 = 1)) (fun e => e.1.2) hne
  obtain ⟨hm0, hi0⟩ := Finset.mem_filter.mp hmem0
  obtain ⟨hm1, hi1⟩ := Finset.mem_filter.mp hmem1
  have hi0' : i0 = 1 := hi0
  have hi1' : i1 = 1 := hi1
  subst hi0'
  subst hi1'
  have hm0' : z ((x0, y0), 1) ≠ 0 := Finsupp.mem_support_iff.mp hm0
  have hm1' : z ((x1, y1), 1) ≠ 0 := Finsupp.mem_support_iff.mp hm1
  have hy0 : y0 = -1 := by
    by_contra hne0
    have hy : y0 + 1 ≠ 0 := by omega
    have hcyc := d1_cycle h x0 (y0 + 1)
    have e1 : z ((x0 - 1, y0 + 1), 0) = 0 := hz _ _ hy
    have e2 : z ((x0, y0 + 1), 0) = 0 := hz _ _ hy
    have e3 : z ((x0, y0 + 1), 1) = 0 := by
      by_contra hne3
      have h' : y0 + 1 ≤ y0 :=
        hmax ((x0, y0 + 1), 1) (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne3, rfl⟩)
      omega
    have e4 : y0 + 1 - 1 = y0 := by omega
    rw [e4, e1, e2, e3] at hcyc
    apply hm0'
    simpa using hcyc
  have hy1 : y1 = 0 := by
    by_contra hne1
    have hcyc := d1_cycle h x1 y1
    have e1 : z ((x1 - 1, y1), 0) = 0 := hz _ _ hne1
    have e2 : z ((x1, y1), 0) = 0 := hz _ _ hne1
    have e3 : z ((x1, y1 - 1), 1) = 0 := by
      by_contra hne3
      have h' : y1 ≤ y1 - 1 :=
        hmin ((x1, y1 - 1), 1) (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne3, rfl⟩)
      omega
    rw [e1, e2, e3] at hcyc
    apply hm1'
    simpa using hcyc
  have hle : y1 ≤ y0 := hmax ((x1, y1), 1) hmem1
  omega

/-- A one-cycle supported on the comb vanishes. -/
theorem comb_zero (z : EdgeChain) (hz : ∀ x y : ℤ, y ≠ 0 → z ((x, y), 0) = 0)
    (h : d1 z = 0) : z = 0 :=
  horizontal_zero z (no_vertical z hz h) h

/-- Every one-cycle is a sum of square boundaries. -/
theorem ker_d1_le : LinearMap.ker d1 ≤ LinearMap.range d2 := by
  intro v hv
  have hv0 : d1 v = 0 := LinearMap.mem_ker.mp hv
  obtain ⟨r, hr, z, hz, hrz⟩ := Submodule.mem_sup.mp (mem_Nsp v)
  have hd1r : d1 r = 0 := by
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hr
    simpa using LinearMap.congr_fun d1_comp_d2 c
  have hd1z : d1 z = 0 := by
    have h : d1 (r + z) = 0 := by
      rw [hrz]
      exact hv0
    rwa [map_add, hd1r, zero_add] at h
  have hzcomb : ∀ x y : ℤ, y ≠ 0 → z ((x, y), 0) = 0 := by
    intro x y hy
    rw [Finsupp.mem_supported'] at hz
    apply hz
    simp [comb, hy]
  have hz0 : z = 0 := comb_zero z hzcomb hd1z
  rw [hz0, add_zero] at hrz
  rw [← hrz]
  exact hr

/-! ### Exactness of the complex and the resolution -/

/-- The square complex is exact. -/
theorem squareComplex_exact : squareComplex.Exact := by
  unfold PermutationComplex.Exact
  refine ⟨range_d0, fun k => ?_⟩
  rcases k with _ | _ | _ | k
  · exact ker_d0_le
  · exact ker_d1_le
  · intro v hv
    have hv' : d2 v = 0 := LinearMap.mem_ker.mp hv
    rw [d2_eq_zero v hv']
    exact zero_mem _
  · intro v _
    have hv : v = 0 := Finsupp.ext fun e => Empty.elim (e : Empty)
    rw [hv]
    exact zero_mem _

/-- The standard free resolution of `ℂ` over `ℤ²` of length two: the augmented chain complex of
the square tiling of the plane. Index `0` is the augmentation point, index `1` the vertices, index
`2` the edges and index `3` the squares. -/
def squareResolution : FreeResolution (Multiplicative (ℤ × ℤ)) 2 where
  cell := squareCell
  action := squareCellAction
  d := squareBoundary
  equivariant := squareBoundary_equivariant
  d_comp_d := squareBoundary_comp
  point := inferInstanceAs (Unique Unit)
  free := squareComplex_free
  exact := squareComplex_exact
  top := inferInstanceAs (IsEmpty Empty)

end TernaryPeriodPolynomials.BoundaryDuality.SquareResolution
