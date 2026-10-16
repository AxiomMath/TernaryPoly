module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineConj

@[expose] public section


/-!
# Flag stabilizers of the plane and line cusps of `Γ(N)` as arithmetic flag groups `gammaNBAt`, for every frame `F`

Formalized by Claude Sonnet 5.5.
Paper: Appendix C, ("Choose a flag in this face. Its
stabilizer contains `N_R` ...").

For `N ≥ 3`, `h ∈ SL₃(ℤ)` and every frame `F ∈ GL₂(ℚ)` (a rational cusp of the binary Levi), there is `g ∈ SL₂(ℤ)` (`exists_cusp_basis`) with

* `faceFlagStab_map_exists_gammaNBAt`: image of the stabilizer of the flag of `F` in the plane group of `h⁻¹Ph` is
  `gammaNBAt N (blockDiag g⁻¹ * h) = Γ(N) ∩ (blockDiag g⁻¹ h)⁻¹ B (blockDiag g⁻¹ h)`;
* `lineFlagStab_map_exists_gammaNBAt`: the same for the line group of `h⁻¹Qh` with `blockDiagQ g⁻¹`;
* `faceFlagStab_map_mapGL`, `lineFlagStab_map_mapGL`: for `F = g ∈ SL₂(ℤ)` this is explicit; `faceFlagStab_one_map`,
  `lineFlagStab_one_map`: `F = 1` gives `gammaNBAt N h`;
* `range_faceFlagStab_map`, `range_lineFlagStab_map`: the set of flag stabilizers over the face is the set of flag groups of the
  conjugate frames `blockDiag g⁻¹ h`.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFacesFull

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3

section Plane

variable (N : ℕ) [NeZero N]

/-- The entries of `blockDiag B * X * blockDiag C` in the Levi block, for `X` in the plane stabilizer. -/
theorem blockDiag_conj_apply10 (B C : SL(2, ℤ)) (X : SL(3, ℤ)) (hX : X ∈ planeStab) :
    ((blockDiag B * X * blockDiag C : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 0 =
      ((B : Matrix (Fin 2) (Fin 2) ℤ) * ((leviBlock X hX : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        (C : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 := by
  obtain ⟨x0, x1, x2⟩ := hX
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp [blockDiag, leviBlock, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blockDiag_conj_apply20 (B C : SL(2, ℤ)) (X : SL(3, ℤ)) (hX : X ∈ planeStab) :
    ((blockDiag B * X * blockDiag C : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
    ((blockDiag B * X * blockDiag C : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 := by
  obtain ⟨x0, x1, x2⟩ := hX
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  refine ⟨?_, ?_⟩ <;> simp [blockDiag, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, x0, x1]

/-- **The stabilizer of the complete flag of a frame `F` is the flag group of a conjugate frame** (planes, `N ≥ 3`). If `g ∈ SL₂(ℤ)`
satisfies `F⁻¹γF` upper triangular `↔ g⁻¹γg` upper triangular (such `g` exists for every `F`, `exists_cusp_basis`), then the
stabilizer in the plane group of `h⁻¹Ph` of the flag of `F` is the arithmetic flag group `Γ(N) ∩ (blockDiag g⁻¹ · h)⁻¹ B (blockDiag g⁻¹ · h)`
of the Borel subgroup `B`. -/
theorem faceFlagStab_map_eq_gammaNBAt (hN : 3 ≤ N) (h : SL(3, ℤ)) (F : GL (Fin 2) ℚ) (g : SL(2, ℤ))
    (hg : ∀ γ : SL(2, ℤ),
      ((F⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ γ * F : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 ↔
        ((g⁻¹ * γ * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) :
    (faceFlagStab N h F).map (gammaNPAt N h).subtype = gammaNBAt N (blockDiag g⁻¹ * h) := by
  ext p
  have hinv : blockDiag g⁻¹ = (blockDiag g)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← blockDiag_mul, inv_mul_cancel, blockDiag_one])
  have hqB : blockDiag g⁻¹ ∈ planeBorel := mem_planeBorel_of_mem_planeStab (blockDiag_mem_planeStab _)
  have key : ∀ p : SL(3, ℤ), ∀ hp : p ∈ gammaNPAt N h,
      (⟨p, hp⟩ : gammaNPAt N h) ∈ faceFlagStab N h F ↔ p ∈ gammaNBAt N (blockDiag g⁻¹ * h) := by
    intro p hp
    have hX : h * p * h⁻¹ ∈ gammaNP N := hp
    have e : blockDiag g⁻¹ * h * p * (blockDiag g⁻¹ * h)⁻¹ =
        blockDiag g⁻¹ * (h * p * h⁻¹) * blockDiag g := by rw [mul_inv_rev, hinv, inv_inv]; group
    rw [mem_gammaNBAt, e]
    have e2 : (blockDiag g⁻¹)⁻¹ = blockDiag g := by rw [hinv, inv_inv]
    have hc := blockDiag_conj_apply10 g⁻¹ g (h * p * h⁻¹) hX.2
    have hd := blockDiag_conj_apply20 g⁻¹ g (h * p * h⁻¹) hX.2
    constructor
    · intro hmem
      have h1 := (hg (leviBlock (h * p * h⁻¹) hX.2)).mp hmem
      have hmemN := (gammaN_normal N).conj_mem _ hX.1 (blockDiag g⁻¹)
      rw [e2] at hmemN
      exact Subgroup.mem_inf.mpr ⟨hmemN, by rw [hc]; exact h1, hd.1, hd.2⟩
    · intro hB
      exact (hg (leviBlock (h * p * h⁻¹) hX.2)).mpr (by rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← hc]; exact (Subgroup.mem_inf.mp hB).2.1)
  constructor
  · rintro ⟨⟨p, hp⟩, hmem, rfl⟩
    exact (key p hp).mp hmem
  · intro hp
    have hp1 : p ∈ gammaNPAt N (blockDiag g⁻¹ * h) := gammaNBAt_le_gammaNPAt hN _ hp
    have hp2 : p ∈ gammaNPAt N h := by rwa [gammaNPAt_mul_left N h _ hqB] at hp1
    exact ⟨⟨p, hp2⟩, (key p hp2).mpr hp, rfl⟩

/-- For every frame `F ∈ GL₂(ℚ)` the stabilizer of its flag in the plane group of `h⁻¹Ph` is a flag group `gammaNBAt` of a conjugate frame:
for `F ≠ 1` the cusps of the binary Levi are reduced to the standard flag by an integral change of basis (`N ≥ 3`). -/
theorem faceFlagStab_map_exists_gammaNBAt (hN : 3 ≤ N) (h : SL(3, ℤ)) (F : GL (Fin 2) ℚ) :
    ∃ g : SL(2, ℤ), (faceFlagStab N h F).map (gammaNPAt N h).subtype = gammaNBAt N (blockDiag g⁻¹ * h) := by
  obtain ⟨g, hg⟩ := exists_cusp_basis F
  exact ⟨g, faceFlagStab_map_eq_gammaNBAt N hN h F g hg⟩

theorem mapGL_conj_apply10 (g γ : SL(2, ℤ)) :
    ((((Matrix.SpecialLinearGroup.mapGL ℚ g)⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ γ *
      Matrix.SpecialLinearGroup.mapGL ℚ g : GL (Fin 2) ℚ)) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 ↔
      ((g⁻¹ * γ * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
  have e : (Matrix.SpecialLinearGroup.mapGL ℚ g)⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ γ *
      Matrix.SpecialLinearGroup.mapGL ℚ g = Matrix.SpecialLinearGroup.mapGL ℚ (g⁻¹ * γ * g) := by
    simp [map_mul, map_inv]
  rw [e, Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  simp

/-- **The flag groups over the plane `h⁻¹Ph`** are exactly the groups `Γ(N) ∩ (q h)⁻¹ B (q h)`, `q = blockDiag g⁻¹`, `g ∈ SL₂(ℤ)`
(the flag of the cusp `g · ∞`). -/
theorem faceFlagStab_map_mapGL (hN : 3 ≤ N) (h : SL(3, ℤ)) (g : SL(2, ℤ)) :
    (faceFlagStab N h (Matrix.SpecialLinearGroup.mapGL ℚ g)).map (gammaNPAt N h).subtype =
      gammaNBAt N (blockDiag g⁻¹ * h) :=
  faceFlagStab_map_eq_gammaNBAt N hN h _ g (fun γ => mapGL_conj_apply10 g γ)

/-- The flag group of the standard frame is the flag group `Γ(N) ∩ h⁻¹ B h`. -/
theorem faceFlagStab_one_map (hN : 3 ≤ N) (h : SL(3, ℤ)) :
    (faceFlagStab N h 1).map (gammaNPAt N h).subtype = gammaNBAt N h := by
  have := faceFlagStab_map_eq_gammaNBAt N hN h 1 1 (fun γ => by simp)
  simpa [blockDiag_one] using this

/-- **Dictionary for plane flags**: the set of stabilizers of complete flags over the plane `h⁻¹Ph` (image in `SL₃(ℤ)`) is the set of
arithmetic flag groups `gammaNBAt N (blockDiag g⁻¹ * h)`, `g ∈ SL₂(ℤ)`. -/
theorem range_faceFlagStab_map (hN : 3 ≤ N) (h : SL(3, ℤ)) :
    Set.range (fun F : GL (Fin 2) ℚ => (faceFlagStab N h F).map (gammaNPAt N h).subtype) =
      Set.range (fun g : SL(2, ℤ) => gammaNBAt N (blockDiag g⁻¹ * h)) := by
  ext K
  constructor
  · rintro ⟨F, rfl⟩
    obtain ⟨g, hg⟩ := faceFlagStab_map_exists_gammaNBAt N hN h F
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨Matrix.SpecialLinearGroup.mapGL ℚ g, faceFlagStab_map_mapGL N hN h g⟩

end Plane

section Line

variable (N : ℕ) [NeZero N]

theorem blockDiagQ_conj_apply10 (B C : SL(2, ℤ)) (X : SL(3, ℤ)) (hX : X ∈ lineStab) :
    ((blockDiagQ B * X * blockDiagQ C : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 =
      ((B : Matrix (Fin 2) (Fin 2) ℤ) * ((leviBlockQ X hX : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        (C : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 := by
  obtain ⟨x0, x1, x2⟩ := hX
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp [blockDiagQ, leviBlockQ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
    Fin.sum_univ_two]

theorem blockDiagQ_conj_apply_col (B C : SL(2, ℤ)) (X : SL(3, ℤ)) (hX : X ∈ lineStab) :
    ((blockDiagQ B * X * blockDiagQ C : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧
    ((blockDiagQ B * X * blockDiagQ C : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 := by
  obtain ⟨x0, x1, x2⟩ := hX
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  refine ⟨?_, ?_⟩ <;> simp [blockDiagQ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, x1, x2]

theorem blockDiagQ_mem_lineBorel (A : SL(2, ℤ)) : blockDiagQ A ∈ lineBorel :=
  ⟨by simp [blockDiagQ], by simp [blockDiagQ]⟩

/-- **Flag stabilizers over a line cusp** (`N ≥ 3`): the stabilizer in the line group of `h⁻¹Qh` of the flag of a frame `F` is the flag
group `Γ(N) ∩ (blockDiagQ g⁻¹ · h)⁻¹ B (blockDiagQ g⁻¹ · h)` for `g ∈ SL₂(ℤ)` with `F⁻¹γF` upper triangular `↔ g⁻¹γg` upper
triangular. -/
theorem lineFlagStab_map_eq_gammaNBAt (hN : 3 ≤ N) (h : SL(3, ℤ)) (F : GL (Fin 2) ℚ) (g : SL(2, ℤ))
    (hg : ∀ γ : SL(2, ℤ),
      ((F⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ γ * F : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 ↔
        ((g⁻¹ * γ * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) :
    (lineFlagStab N h F).map (gammaNQAt N h).subtype = gammaNBAt N (blockDiagQ g⁻¹ * h) := by
  ext p
  have hinv : blockDiagQ g⁻¹ = (blockDiagQ g)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← blockDiagQ_mul, inv_mul_cancel, blockDiagQ_one])
  have hqB : blockDiagQ g⁻¹ ∈ lineBorel := blockDiagQ_mem_lineBorel _
  have key : ∀ p : SL(3, ℤ), ∀ hp : p ∈ gammaNQAt N h,
      (⟨p, hp⟩ : gammaNQAt N h) ∈ lineFlagStab N h F ↔ p ∈ gammaNBAt N (blockDiagQ g⁻¹ * h) := by
    intro p hp
    have hX : h * p * h⁻¹ ∈ gammaNQ N := hp
    have e : blockDiagQ g⁻¹ * h * p * (blockDiagQ g⁻¹ * h)⁻¹ =
        blockDiagQ g⁻¹ * (h * p * h⁻¹) * blockDiagQ g := by rw [mul_inv_rev, hinv, inv_inv]; group
    have e2 : (blockDiagQ g⁻¹)⁻¹ = blockDiagQ g := by rw [hinv, inv_inv]
    rw [mem_gammaNBAt, e]
    have hc := blockDiagQ_conj_apply10 g⁻¹ g (h * p * h⁻¹) hX.2
    have hd := blockDiagQ_conj_apply_col g⁻¹ g (h * p * h⁻¹) hX.2
    constructor
    · intro hmem
      have h1 := (hg (leviBlockQ (h * p * h⁻¹) hX.2)).mp hmem
      have hmemN := (gammaN_normal N).conj_mem _ hX.1 (blockDiagQ g⁻¹)
      rw [e2] at hmemN
      exact Subgroup.mem_inf.mpr ⟨hmemN, hd.1, hd.2, by rw [hc]; exact h1⟩
    · intro hB
      exact (hg (leviBlockQ (h * p * h⁻¹) hX.2)).mpr (by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← hc]
        exact (Subgroup.mem_inf.mp hB).2.2.2)
  constructor
  · rintro ⟨⟨p, hp⟩, hmem, rfl⟩
    exact (key p hp).mp hmem
  · intro hp
    have hp1 : p ∈ gammaNQAt N (blockDiagQ g⁻¹ * h) := gammaNBAt_le_gammaNQAt hN _ hp
    have hp2 : p ∈ gammaNQAt N h := by rwa [gammaNQAt_mul_left N h _ hqB] at hp1
    exact ⟨⟨p, hp2⟩, (key p hp2).mpr hp, rfl⟩

theorem lineFlagStab_map_exists_gammaNBAt (hN : 3 ≤ N) (h : SL(3, ℤ)) (F : GL (Fin 2) ℚ) :
    ∃ g : SL(2, ℤ), (lineFlagStab N h F).map (gammaNQAt N h).subtype = gammaNBAt N (blockDiagQ g⁻¹ * h) := by
  obtain ⟨g, hg⟩ := exists_cusp_basis F
  exact ⟨g, lineFlagStab_map_eq_gammaNBAt N hN h F g hg⟩

theorem lineFlagStab_map_mapGL (hN : 3 ≤ N) (h : SL(3, ℤ)) (g : SL(2, ℤ)) :
    (lineFlagStab N h (Matrix.SpecialLinearGroup.mapGL ℚ g)).map (gammaNQAt N h).subtype =
      gammaNBAt N (blockDiagQ g⁻¹ * h) :=
  lineFlagStab_map_eq_gammaNBAt N hN h _ g (fun γ => mapGL_conj_apply10 g γ)

theorem lineFlagStab_one_map (hN : 3 ≤ N) (h : SL(3, ℤ)) :
    (lineFlagStab N h 1).map (gammaNQAt N h).subtype = gammaNBAt N h := by
  have := lineFlagStab_map_eq_gammaNBAt N hN h 1 1 (fun γ => by simp)
  simpa [blockDiagQ_one] using this

/-- **Dictionary for line flags**: the stabilizers of complete flags over the line `h⁻¹Qh` are the flag groups
`gammaNBAt N (blockDiagQ g⁻¹ * h)`, `g ∈ SL₂(ℤ)`. -/
theorem range_lineFlagStab_map (hN : 3 ≤ N) (h : SL(3, ℤ)) :
    Set.range (fun F : GL (Fin 2) ℚ => (lineFlagStab N h F).map (gammaNQAt N h).subtype) =
      Set.range (fun g : SL(2, ℤ) => gammaNBAt N (blockDiagQ g⁻¹ * h)) := by
  ext K
  constructor
  · rintro ⟨F, rfl⟩
    obtain ⟨g, hg⟩ := lineFlagStab_map_exists_gammaNBAt N hN h F
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨Matrix.SpecialLinearGroup.mapGL ℚ g, lineFlagStab_map_mapGL N hN h g⟩

end Line

end TernaryPeriodPolynomials.Argument.GammaNFacesFull
