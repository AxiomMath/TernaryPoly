module

public import TernaryPeriodPolynomials.Building.Integer.Exactness

@[expose] public section


/-! Explicit finite-chain contraction for the whole infinite integer path. -/

noncomputable section
namespace TernaryPoly.IntegerPathExactness
open IntegerGridExactness (signedSum signedSum_add_one linearMap_signedSum signedSum_telescope)

abbrev C₀ := ℤ →₀ ℚ
abbrev C₁ := ℤ →₀ ℚ

def vertex (n : ℤ) : C₀ := Finsupp.single n 1
def edge (n : ℤ) : C₁ := Finsupp.single n 1

/-- Each positively oriented unit edge has its literal two integer endpoints. -/
def boundary : C₁ →ₗ[ℚ] C₀ :=
  Finsupp.linearCombination ℚ (fun n => vertex (n+1) - vertex n)

@[simp] theorem boundary_single (n : ℤ) (q : ℚ) :
    boundary (Finsupp.single n q) = q • (vertex (n+1) - vertex n) :=
  Finsupp.linearCombination_single ℚ q n

@[simp] theorem boundary_edge (n : ℤ) : boundary (edge n) = vertex (n+1) - vertex n := by
  simp only [edge,boundary_single,one_smul]

/-- Total coefficient sum on finite integer vertex chains. -/
def augmentation : C₀ →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ (fun _ => (1 : ℚ))

@[simp] theorem augmentation_single (n : ℤ) (q : ℚ) :
    augmentation (Finsupp.single n q) = q := by simp [augmentation]

@[simp] theorem augmentation_vertex (n : ℤ) : augmentation (vertex n) = 1 :=
  augmentation_single n 1

theorem augmentation_eq_sum (z : C₀) : augmentation z = z.sum (fun _ q => q) := by
  simp only [augmentation,Finsupp.linearCombination_apply,smul_eq_mul,mul_one]

/-- The actual finite signed path from zero to any positive or negative integer. -/
def path (n : ℤ) : C₁ := signedSum edge n

theorem path_add_one (n : ℤ) : path (n+1) = path n + edge n := signedSum_add_one edge n

theorem boundary_path (n : ℤ) : boundary (path n) = vertex n - vertex 0 := by
  rw [path,linearMap_signedSum]
  simp only [boundary_edge]
  exact signedSum_telescope vertex n

/-- Explicit finite path filling, extended linearly. -/
def pathLinear : C₀ →ₗ[ℚ] C₁ := Finsupp.linearCombination ℚ path

@[simp] theorem pathLinear_single (n : ℤ) (q : ℚ) :
    pathLinear (Finsupp.single n q) = q • path n := Finsupp.linearCombination_single ℚ q n

@[simp] theorem pathLinear_vertex (n : ℤ) : pathLinear (vertex n) = path n := by
  simp only [vertex,pathLinear_single,one_smul]

/-- The finite path contraction is valid on every finite vertex chain. -/
theorem boundary_pathLinear (z : C₀) :
    boundary (pathLinear z) = z - augmentation z • vertex 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,zero_smul,sub_self]
  | add x y hx hy => simp only [map_add,hx,hy,add_smul]; abel
  | single n q =>
    simp only [pathLinear_single,map_smul,boundary_path,augmentation_single,smul_sub]
    rw [vertex,Finsupp.smul_single,smul_eq_mul,mul_one]

/-- Adjacent signed paths differ by exactly their connecting edge. -/
theorem pathLinear_boundary_edge (n : ℤ) : pathLinear (boundary (edge n)) = edge n := by
  rw [boundary_edge,map_sub,pathLinear_vertex,pathLinear_vertex,path_add_one,add_sub_cancel_left]

/-- Path filling is an actual left inverse of the finite edge boundary. -/
theorem pathLinear_boundary (c : C₁) : pathLinear (boundary c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | single n q =>
    have h : Finsupp.single n q = q • edge n := by simp [edge]
    rw [h,map_smul,map_smul,pathLinear_boundary_edge]

theorem augmentation_boundary (c : C₁) : augmentation (boundary c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy,add_zero]
  | single n q =>
    simp only [boundary_single,map_smul,map_sub,augmentation_vertex,sub_self,smul_zero]

/-- Every finite zero-sum vertex chain has the displayed finite signed-path filler. -/
theorem ker_augmentation_eq_range_boundary : LinearMap.ker augmentation = boundary.range := by
  ext z
  constructor
  · intro hz
    refine ⟨pathLinear z,?_⟩
    rw [boundary_pathLinear,LinearMap.mem_ker.mp hz,zero_smul,sub_zero]
  · rintro ⟨c,rfl⟩
    exact augmentation_boundary c

/-- The infinite path has no nonzero finitely supported edge cycles. -/
theorem boundary_injective : Function.Injective boundary :=
  (show Function.LeftInverse pathLinear boundary from pathLinear_boundary).injective

theorem ker_boundary_eq_bot : LinearMap.ker boundary = ⊥ :=
  LinearMap.ker_eq_bot.mpr boundary_injective

theorem eq_zero_of_boundary_eq_zero {c : C₁} (hc : boundary c = 0) : c = 0 :=
  boundary_injective (hc.trans (map_zero boundary).symm)

end TernaryPoly.IntegerPathExactness
