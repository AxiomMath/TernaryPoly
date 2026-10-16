module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Data.Int.Init
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.Abel
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Control.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.IntegerGridExactness

section SignedSum
variable {E F : Type*} [AddCommGroup E] [AddCommGroup F]

/-- A finite oriented sum from zero to an arbitrary integer endpoint. -/
def signedSum (f : ℤ → E) : ℤ → E
  | .ofNat n => ∑ i ∈ Finset.range n, f (i : ℤ)
  | .negSucc n => -(∑ i ∈ Finset.range (n+1), f (-((i+1 : ℕ) : ℤ)))

@[simp] theorem signedSum_zero (f : ℤ → E) : signedSum f 0 = 0 := by
  simp [signedSum]

/-- Adding one endpoint adds precisely its oriented unit interval. -/
theorem signedSum_add_one (f : ℤ → E) (n : ℤ) :
    signedSum f (n+1) = signedSum f n + f n := by
  cases n with
  | ofNat n =>
    change signedSum f ((n+1 : ℕ) : ℤ) = _
    simp only [signedSum, Finset.sum_range_succ]
    rfl
  | negSucc n =>
    cases n with
    | zero => simp [signedSum]
    | succ n =>
      have hn : Int.negSucc (n+1) + 1 = Int.negSucc n := by omega
      rw [hn]
      simp only [signedSum, Finset.sum_range_succ]
      have he : -((n+1+1 : ℕ) : ℤ) = Int.negSucc (n+1) := by omega
      rw [he]
      abel

/-- Additive maps commute with every finite oriented integer sum. -/
theorem map_signedSum (T : E →+ F) (f : ℤ → E) (n : ℤ) :
    T (signedSum f n) = signedSum (fun i => T (f i)) n := by
  cases n <;> simp only [signedSum, map_sum, map_neg]

theorem signedSum_add (f g : ℤ → E) (n : ℤ) :
    signedSum (fun i => f i + g i) n = signedSum f n + signedSum g n := by
  cases n <;> simp only [signedSum, Finset.sum_add_distrib, neg_add]

theorem signedSum_sub (f g : ℤ → E) (n : ℤ) :
    signedSum (fun i => f i - g i) n = signedSum f n - signedSum g n := by
  cases n <;> simp only [signedSum, Finset.sum_sub_distrib, neg_sub_neg, neg_sub]

theorem signedSum_neg (f : ℤ → E) (n : ℤ) :
    signedSum (fun i => -f i) n = -signedSum f n := by
  cases n <;> simp only [signedSum, Finset.sum_neg_distrib, neg_neg]

theorem linearMap_signedSum [Module ℚ E] [Module ℚ F]
    (T : E →ₗ[ℚ] F) (f : ℤ → E) (n : ℤ) :
    T (signedSum f n) = signedSum (fun i => T (f i)) n :=
  map_signedSum T.toAddMonoidHom f n

/-- Telescoping holds for every positive or negative integer endpoint. -/
theorem signedSum_telescope (f : ℤ → E) (n : ℤ) :
    signedSum (fun i => f (i+1) - f i) n = f n - f 0 := by
  induction n using Int.induction_on with
  | zero => simp only [signedSum_zero, sub_self]
  | succ n ih =>
    rw [signedSum_add_one, ih]
    abel
  | pred n ih =>
    have h := signedSum_add_one (fun i => f (i+1) - f i) (-(n : ℤ)-1)
    have hn : -(n : ℤ)-1+1 = -(n : ℤ) := by omega
    rw [hn, ih] at h
    apply add_right_cancel (b := f (- (n : ℤ)) - f (- (n : ℤ) - 1))
    rw [← h]
    abel
end SignedSum

abbrev Vertex := ℤ × ℤ
abbrev Edge := Vertex × Fin 2
abbrev C₀ := Vertex →₀ ℚ
abbrev C₁ := Edge →₀ ℚ
abbrev C₂ := Vertex →₀ ℚ

/-- The head of a horizontal or vertical positively oriented grid edge. -/
def edgeHead (e : Edge) : Vertex :=
  if e.2 = 0 then (e.1.1+1,e.1.2) else (e.1.1,e.1.2+1)

def vertex (p : Vertex) : C₀ := Finsupp.single p 1
def horizontal (p : Vertex) : C₁ := Finsupp.single (p,0) 1
def vertical (p : Vertex) : C₁ := Finsupp.single (p,1) 1
def square (p : Vertex) : C₂ := Finsupp.single p 1

/-- The genuine endpoint-minus-start boundary of a finite grid edge chain. -/
def boundary₁ : C₁ →ₗ[ℚ] C₀ :=
  Finsupp.linearCombination ℚ (fun e => vertex (edgeHead e) - vertex e.1)

@[simp] theorem boundary₁_single (e : Edge) (q : ℚ) :
    boundary₁ (Finsupp.single e q) = q • (vertex (edgeHead e) - vertex e.1) :=
  Finsupp.linearCombination_single ℚ q e

@[simp] theorem boundary₁_horizontal (p : Vertex) :
    boundary₁ (horizontal p) = vertex (p.1+1,p.2) - vertex p := by
  simp [horizontal, boundary₁, edgeHead]

@[simp] theorem boundary₁_vertical (p : Vertex) :
    boundary₁ (vertical p) = vertex (p.1,p.2+1) - vertex p := by
  simp [vertical, boundary₁, edgeHead]

/-- The four oriented edges around a positively oriented unit square. -/
def squareBoundary (p : Vertex) : C₁ :=
  horizontal p + vertical (p.1+1,p.2) - horizontal (p.1,p.2+1) - vertical p

/-- The genuine unit-square boundary, extended to all finite square chains. -/
def boundary₂ : C₂ →ₗ[ℚ] C₁ := Finsupp.linearCombination ℚ squareBoundary

@[simp] theorem boundary₂_single (p : Vertex) (q : ℚ) :
    boundary₂ (Finsupp.single p q) = q • squareBoundary p :=
  Finsupp.linearCombination_single ℚ q p

@[simp] theorem boundary₂_square (p : Vertex) : boundary₂ (square p) = squareBoundary p := by
  simp only [square, boundary₂_single, one_smul]

@[simp] theorem boundary₁_squareBoundary (p : Vertex) : boundary₁ (squareBoundary p) = 0 := by
  simp only [squareBoundary, map_sub, map_add, boundary₁_horizontal, boundary₁_vertical]
  abel

/-- Every finite sum of unit-square boundaries is a cycle. -/
theorem boundary₁_boundary₂ (z : C₂) : boundary₁ (boundary₂ z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | single p q => simp only [boundary₂_single, map_smul, boundary₁_squareBoundary, smul_zero]

theorem boundary_comp_boundary : boundary₁.comp boundary₂ = 0 := by
  apply LinearMap.ext
  intro z
  exact boundary₁_boundary₂ z

/-- Total coefficient sum of an actual finite vertex chain. -/
def augmentation : C₀ →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ (fun _ => (1 : ℚ))

@[simp] theorem augmentation_single (p : Vertex) (q : ℚ) :
    augmentation (Finsupp.single p q) = q := by
  simp [augmentation]

theorem augmentation_eq_sum (z : C₀) : augmentation z = z.sum (fun _ q => q) := by
  simp only [augmentation, Finsupp.linearCombination_apply, smul_eq_mul, mul_one]

@[simp] theorem augmentation_vertex (p : Vertex) : augmentation (vertex p) = 1 :=
  augmentation_single p 1

/-- Every edge boundary has total coefficient zero. -/
theorem augmentation_boundary₁ (z : C₁) : augmentation (boundary₁ z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | single p q =>
    simp only [boundary₁_single, map_smul, map_sub, augmentation_vertex, sub_self, smul_zero]

/-- The finite path to `(x,y)` travels horizontally at height zero, then vertically at `x`. -/
def path (p : Vertex) : C₁ :=
  signedSum (fun i => horizontal (i,0)) p.1 + signedSum (fun j => vertical (p.1,j)) p.2

/-- The path boundary is the endpoint minus the origin. -/
theorem boundary₁_path (p : Vertex) : boundary₁ (path p) = vertex p - vertex (0,0) := by
  rw [path, map_add, linearMap_signedSum boundary₁,
    linearMap_signedSum boundary₁]
  simp only [boundary₁_horizontal, boundary₁_vertical]
  rw [signedSum_telescope (fun i => vertex (i,0)),
    signedSum_telescope (fun j => vertex (p.1,j))]
  abel

/-- Linear extension of the chosen finite paths. -/
def pathLinear : C₀ →ₗ[ℚ] C₁ := Finsupp.linearCombination ℚ path

@[simp] theorem pathLinear_single (p : Vertex) (q : ℚ) :
    pathLinear (Finsupp.single p q) = q • path p := Finsupp.linearCombination_single ℚ q p

@[simp] theorem pathLinear_vertex (p : Vertex) : pathLinear (vertex p) = path p := by
  simp only [vertex, pathLinear_single, one_smul]

/-- Paths give a contracting identity for all finite vertex chains. -/
theorem boundary₁_pathLinear (z : C₀) :
    boundary₁ (pathLinear z) = z - augmentation z • vertex (0,0) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero, zero_smul, sub_self]
  | add x y hx hy =>
    simp only [map_add, hx, hy, add_smul]
    abel
  | single p q =>
    simp only [pathLinear_single, map_smul, boundary₁_path, augmentation_single, smul_sub]
    rw [vertex, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Every finite vertex chain of total coefficient zero is an actual edge boundary. -/
theorem ker_augmentation_eq_range_boundary₁ :
    LinearMap.ker augmentation = LinearMap.range boundary₁ := by
  ext z
  constructor
  · intro hz
    refine ⟨pathLinear z, ?_⟩
    rw [boundary₁_pathLinear, LinearMap.mem_ker.mp hz, zero_smul, sub_zero]
  · rintro ⟨c,rfl⟩
    exact augmentation_boundary₁ c

/-- A finite vertical strip of unit squares, with signed orientation for negative heights. -/
def strip (p : Vertex) : C₂ := signedSum (fun j => square (p.1,j)) p.2

/-- The two sides of the finite strip telescope to its horizontal endpoints. -/
theorem boundary₂_strip (p : Vertex) :
    boundary₂ (strip p) = horizontal (p.1,0) - horizontal p +
      (signedSum (fun j => vertical (p.1+1,j)) p.2 -
        signedSum (fun j => vertical (p.1,j)) p.2) := by
  rw [strip, linearMap_signedSum boundary₂]
  simp only [boundary₂_square]
  have h : (fun j => squareBoundary (p.1,j)) =
      (fun j => -(horizontal (p.1,j+1) - horizontal (p.1,j)) +
        (vertical (p.1+1,j) - vertical (p.1,j))) := by
    funext j
    unfold squareBoundary
    abel
  rw [h, signedSum_add, signedSum_neg,
    signedSum_telescope (fun j => horizontal (p.1,j)), signedSum_sub, neg_sub]

/-- Each horizontal closed edge is filled by minus its vertical strip; vertical ones need no squares. -/
def edgeFilling (e : Edge) : C₂ := if e.2 = 0 then -strip e.1 else 0

/-- Every edge differs from the chosen path between its endpoints by an explicit square boundary. -/
theorem boundary₂_edgeFilling (e : Edge) :
    boundary₂ (edgeFilling e) = Finsupp.single e 1 -
      pathLinear (boundary₁ (Finsupp.single e 1)) := by
  rcases e with ⟨p,d⟩
  fin_cases d
  · change boundary₂ (-strip p) = horizontal p - pathLinear (boundary₁ (horizontal p))
    rw [map_neg, boundary₂_strip, boundary₁_horizontal, map_sub,
      pathLinear_vertex, pathLinear_vertex]
    dsimp only [path]
    rw [signedSum_add_one]
    abel
  · change boundary₂ 0 = vertical p - pathLinear (boundary₁ (vertical p))
    rw [map_zero, boundary₁_vertical, map_sub, pathLinear_vertex, pathLinear_vertex]
    dsimp only [path]
    rw [signedSum_add_one]
    abel

/-- Linear extension gives a finite square filling for every finite edge chain's closed part. -/
def filling : C₁ →ₗ[ℚ] C₂ := Finsupp.linearCombination ℚ edgeFilling

@[simp] theorem filling_single (e : Edge) (q : ℚ) :
    filling (Finsupp.single e q) = q • edgeFilling e :=
  Finsupp.linearCombination_single ℚ q e

/-- A chain homotopy identity valid for every finite chain on the infinite integer grid. -/
theorem boundary₂_filling (z : C₁) :
    boundary₂ (filling z) = z - pathLinear (boundary₁ z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero, sub_self]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    abel
  | single e q =>
    rw [filling_single, map_smul, boundary₂_edgeFilling, smul_sub,
      Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [boundary₁_single, boundary₁_single, one_smul, map_smul]

/-- Every finitely supported cycle in the infinite square grid bounds a finitely supported square chain. -/
theorem ker_boundary₁_eq_range_boundary₂ :
    LinearMap.ker boundary₁ = LinearMap.range boundary₂ := by
  ext z
  constructor
  · intro hz
    refine ⟨filling z, ?_⟩
    rw [boundary₂_filling, LinearMap.mem_ker.mp hz, map_zero, sub_zero]
  · rintro ⟨c,rfl⟩
    exact boundary₁_boundary₂ c

end TernaryPoly.IntegerGridExactness
