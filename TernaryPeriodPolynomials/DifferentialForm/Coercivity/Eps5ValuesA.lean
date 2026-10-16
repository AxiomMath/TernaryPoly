module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5Values

@[expose] public section



/-! `eps5_v_*` permutation-value
simp lemmas, 1-60 in lexicographic order of (p0,p1,p2,p3,p4). Each is proved by the single
uniform pattern: build the permutation as a
concrete `Equiv.Perm (Fin 5)`, bridge via `eps5_perm`, `decide` the sign, cast with `norm_num`.
-/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

@[simp] theorem eps5_v_0_1_2_3_4 : eps5 0 1 2 3 4 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,1,2,3,4], ![0,1,2,3,4], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 1 2 3 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_1_2_4_3 : eps5 0 1 2 4 3 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,1,2,4,3], ![0,1,2,4,3], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 1 2 4 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_1_3_2_4 : eps5 0 1 3 2 4 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,1,3,2,4], ![0,1,3,2,4], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 1 3 2 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_1_3_4_2 : eps5 0 1 3 4 2 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,1,3,4,2], ![0,1,4,2,3], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 1 3 4 2 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_1_4_2_3 : eps5 0 1 4 2 3 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,1,4,2,3], ![0,1,3,4,2], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 1 4 2 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_1_4_3_2 : eps5 0 1 4 3 2 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,1,4,3,2], ![0,1,4,3,2], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 1 4 3 2 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_2_1_3_4 : eps5 0 2 1 3 4 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,2,1,3,4], ![0,2,1,3,4], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 2 1 3 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_2_1_4_3 : eps5 0 2 1 4 3 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,2,1,4,3], ![0,2,1,4,3], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 2 1 4 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_2_3_1_4 : eps5 0 2 3 1 4 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,2,3,1,4], ![0,3,1,2,4], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 2 3 1 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_2_3_4_1 : eps5 0 2 3 4 1 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,2,3,4,1], ![0,4,1,2,3], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 2 3 4 1 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_2_4_1_3 : eps5 0 2 4 1 3 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,2,4,1,3], ![0,3,1,4,2], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 2 4 1 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_2_4_3_1 : eps5 0 2 4 3 1 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,2,4,3,1], ![0,4,1,3,2], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 2 4 3 1 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_3_1_2_4 : eps5 0 3 1 2 4 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,3,1,2,4], ![0,2,3,1,4], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 3 1 2 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_3_1_4_2 : eps5 0 3 1 4 2 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,3,1,4,2], ![0,2,4,1,3], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 3 1 4 2 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_3_2_1_4 : eps5 0 3 2 1 4 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,3,2,1,4], ![0,3,2,1,4], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 3 2 1 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_3_2_4_1 : eps5 0 3 2 4 1 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,3,2,4,1], ![0,4,2,1,3], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 3 2 4 1 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_3_4_1_2 : eps5 0 3 4 1 2 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,3,4,1,2], ![0,3,4,1,2], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 3 4 1 2 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_3_4_2_1 : eps5 0 3 4 2 1 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,3,4,2,1], ![0,4,3,1,2], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 3 4 2 1 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_4_1_2_3 : eps5 0 4 1 2 3 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,4,1,2,3], ![0,2,3,4,1], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 4 1 2 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_4_1_3_2 : eps5 0 4 1 3 2 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,4,1,3,2], ![0,2,4,3,1], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 4 1 3 2 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_4_2_1_3 : eps5 0 4 2 1 3 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,4,2,1,3], ![0,3,2,4,1], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 4 2 1 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_4_2_3_1 : eps5 0 4 2 3 1 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,4,2,3,1], ![0,4,2,3,1], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 4 2 3 1 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_4_3_1_2 : eps5 0 4 3 1 2 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,4,3,1,2], ![0,3,4,2,1], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 4 3 1 2 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_0_4_3_2_1 : eps5 0 4 3 2 1 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![0,4,3,2,1], ![0,4,3,2,1], by decide, by decide⟩
  have key : eps5 (0 : Fin 5) 4 3 2 1 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_0_2_3_4 : eps5 1 0 2 3 4 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,0,2,3,4], ![1,0,2,3,4], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 0 2 3 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_0_2_4_3 : eps5 1 0 2 4 3 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,0,2,4,3], ![1,0,2,4,3], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 0 2 4 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_0_3_2_4 : eps5 1 0 3 2 4 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,0,3,2,4], ![1,0,3,2,4], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 0 3 2 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_0_3_4_2 : eps5 1 0 3 4 2 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,0,3,4,2], ![1,0,4,2,3], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 0 3 4 2 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_0_4_2_3 : eps5 1 0 4 2 3 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,0,4,2,3], ![1,0,3,4,2], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 0 4 2 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_0_4_3_2 : eps5 1 0 4 3 2 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,0,4,3,2], ![1,0,4,3,2], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 0 4 3 2 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_2_0_3_4 : eps5 1 2 0 3 4 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,2,0,3,4], ![2,0,1,3,4], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 2 0 3 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_2_0_4_3 : eps5 1 2 0 4 3 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,2,0,4,3], ![2,0,1,4,3], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 2 0 4 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_2_3_0_4 : eps5 1 2 3 0 4 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,2,3,0,4], ![3,0,1,2,4], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 2 3 0 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_2_3_4_0 : eps5 1 2 3 4 0 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,2,3,4,0], ![4,0,1,2,3], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 2 3 4 0 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_2_4_0_3 : eps5 1 2 4 0 3 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,2,4,0,3], ![3,0,1,4,2], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 2 4 0 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_2_4_3_0 : eps5 1 2 4 3 0 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,2,4,3,0], ![4,0,1,3,2], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 2 4 3 0 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_3_0_2_4 : eps5 1 3 0 2 4 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,3,0,2,4], ![2,0,3,1,4], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 3 0 2 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_3_0_4_2 : eps5 1 3 0 4 2 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,3,0,4,2], ![2,0,4,1,3], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 3 0 4 2 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_3_2_0_4 : eps5 1 3 2 0 4 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,3,2,0,4], ![3,0,2,1,4], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 3 2 0 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_3_2_4_0 : eps5 1 3 2 4 0 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,3,2,4,0], ![4,0,2,1,3], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 3 2 4 0 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_3_4_0_2 : eps5 1 3 4 0 2 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,3,4,0,2], ![3,0,4,1,2], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 3 4 0 2 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_3_4_2_0 : eps5 1 3 4 2 0 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,3,4,2,0], ![4,0,3,1,2], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 3 4 2 0 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_4_0_2_3 : eps5 1 4 0 2 3 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,4,0,2,3], ![2,0,3,4,1], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 4 0 2 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_4_0_3_2 : eps5 1 4 0 3 2 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,4,0,3,2], ![2,0,4,3,1], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 4 0 3 2 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_4_2_0_3 : eps5 1 4 2 0 3 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,4,2,0,3], ![3,0,2,4,1], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 4 2 0 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_4_2_3_0 : eps5 1 4 2 3 0 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,4,2,3,0], ![4,0,2,3,1], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 4 2 3 0 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_4_3_0_2 : eps5 1 4 3 0 2 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,4,3,0,2], ![3,0,4,2,1], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 4 3 0 2 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_1_4_3_2_0 : eps5 1 4 3 2 0 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![1,4,3,2,0], ![4,0,3,2,1], by decide, by decide⟩
  have key : eps5 (1 : Fin 5) 4 3 2 0 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_2_0_1_3_4 : eps5 2 0 1 3 4 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![2,0,1,3,4], ![1,2,0,3,4], by decide, by decide⟩
  have key : eps5 (2 : Fin 5) 0 1 3 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_2_0_1_4_3 : eps5 2 0 1 4 3 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![2,0,1,4,3], ![1,2,0,4,3], by decide, by decide⟩
  have key : eps5 (2 : Fin 5) 0 1 4 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_2_0_3_1_4 : eps5 2 0 3 1 4 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![2,0,3,1,4], ![1,3,0,2,4], by decide, by decide⟩
  have key : eps5 (2 : Fin 5) 0 3 1 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_2_0_3_4_1 : eps5 2 0 3 4 1 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![2,0,3,4,1], ![1,4,0,2,3], by decide, by decide⟩
  have key : eps5 (2 : Fin 5) 0 3 4 1 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_2_0_4_1_3 : eps5 2 0 4 1 3 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![2,0,4,1,3], ![1,3,0,4,2], by decide, by decide⟩
  have key : eps5 (2 : Fin 5) 0 4 1 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_2_0_4_3_1 : eps5 2 0 4 3 1 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![2,0,4,3,1], ![1,4,0,3,2], by decide, by decide⟩
  have key : eps5 (2 : Fin 5) 0 4 3 1 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_2_1_0_3_4 : eps5 2 1 0 3 4 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![2,1,0,3,4], ![2,1,0,3,4], by decide, by decide⟩
  have key : eps5 (2 : Fin 5) 1 0 3 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_2_1_0_4_3 : eps5 2 1 0 4 3 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![2,1,0,4,3], ![2,1,0,4,3], by decide, by decide⟩
  have key : eps5 (2 : Fin 5) 1 0 4 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_2_1_3_0_4 : eps5 2 1 3 0 4 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![2,1,3,0,4], ![3,1,0,2,4], by decide, by decide⟩
  have key : eps5 (2 : Fin 5) 1 3 0 4 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_2_1_3_4_0 : eps5 2 1 3 4 0 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![2,1,3,4,0], ![4,1,0,2,3], by decide, by decide⟩
  have key : eps5 (2 : Fin 5) 1 3 4 0 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_2_1_4_0_3 : eps5 2 1 4 0 3 = -1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![2,1,4,0,3], ![3,1,0,4,2], by decide, by decide⟩
  have key : eps5 (2 : Fin 5) 1 4 0 3 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = -1 := by decide
  rw [hsign]
  norm_num

@[simp] theorem eps5_v_2_1_4_3_0 : eps5 2 1 4 3 0 = 1 := by
  let σ : Equiv.Perm (Fin 5) := ⟨![2,1,4,3,0], ![4,1,0,3,2], by decide, by decide⟩
  have key : eps5 (2 : Fin 5) 1 4 3 0 = (Equiv.Perm.sign σ : ℝ) := eps5_perm (σ := σ)
  rw [key]
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  rw [hsign]
  norm_num


end TernaryPeriodPolynomials.Argument.Coercivity
