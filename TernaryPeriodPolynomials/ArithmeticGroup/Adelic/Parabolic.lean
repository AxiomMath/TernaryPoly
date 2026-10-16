module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Matrices

@[expose] public section




/-! Actual block parabolic subgroups over commutative rings, including the genuine adeles. -/
noncomputable section
namespace GeneralEisenstein.Adelic
open Matrix
variable {R : Type*} [CommRing R]

/-- Cancellation by a scalar with an actual multiplicative inverse, without a field assumption. -/
theorem zero_of_unit_corner {a b c : R} (hab : a * b = 1) (hac : a * c = 0) : c = 0 := by
  calc
    c = (a*b)*c := by rw [hab, one_mul]
    _ = b*(a*c) := by ring
    _ = 0 := by rw [hac, mul_zero]

/-- Actual upper (2,1) block matrices are closed under products over any commutative ring. -/
theorem inPlane_mul {g h : GL3 R} (hg : InPlaneParabolic g) (hh : InPlaneParabolic h) :
    InPlaneParabolic (g*h) := by
  constructor <;> simp [Units.val_mul, Matrix.mul_apply,
    Fin.sum_univ_three, hg.1, hg.2, hh.1, hh.2]

/-- The inverse of an actual upper (2,1) block unit has the same zero block, even over adeles. -/
theorem inPlane_inv {g : GL3 R} (hg : InPlaneParabolic g) : InPlaneParabolic g⁻¹ := by
  have hr (j : Fin 3) := congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 2 j) g.mul_inv
  have hc : g.val 2 2 * g.inv 2 2 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2] using hr 2
  have hz (j : Fin 3) (hj : j ≠ 2) : g.val 2 2 * g.inv 2 j = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2, hj, Ne.symm hj] using hr j
  exact ⟨zero_of_unit_corner hc (hz 0 (by decide)), zero_of_unit_corner hc (hz 1 (by decide))⟩

/-- The actual upper plane parabolic in the genuine general linear group over any commutative ring. -/
def planeParabolic (R : Type*) [CommRing R] : Subgroup (GL3 R) where
  carrier := InPlaneParabolic
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := inPlane_mul
  inv_mem' := inPlane_inv

/-- The actual upper line parabolic condition is the literal lower two entries of its first column. -/
def InLineParabolic (g : GL3 R) : Prop := g.val 1 0 = 0 ∧ g.val 2 0 = 0

/-- Actual upper (1,2) block matrices are closed under products. -/
theorem inLine_mul {g h : GL3 R} (hg : InLineParabolic g) (hh : InLineParabolic h) :
    InLineParabolic (g*h) := by
  constructor <;> simp [Units.val_mul, Matrix.mul_apply,
    Fin.sum_univ_three, hg.1, hg.2, hh.1, hh.2]

/-- The inverse of an actual upper (1,2) block unit has its actual prescribed zero block. -/
theorem inLine_inv {g : GL3 R} (hg : InLineParabolic g) : InLineParabolic g⁻¹ := by
  have hr (i : Fin 3) := congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A i 0) g.inv_mul
  have hc : g.val 0 0 * g.inv 0 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2, mul_comm] using hr 0
  have hz (i : Fin 3) (hi : i ≠ 0) : g.val 0 0 * g.inv i 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2, hi, mul_comm] using hr i
  exact ⟨zero_of_unit_corner hc (hz 1 (by decide)), zero_of_unit_corner hc (hz 2 (by decide))⟩

/-- The actual upper line parabolic in the genuine general linear group. -/
def lineParabolic (R : Type*) [CommRing R] : Subgroup (GL3 R) where
  carrier := InLineParabolic
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := inLine_mul
  inv_mem' := inLine_inv

/-- The actual adelic plane parabolic subgroup. -/
abbrev Plane := planeParabolic Adeles

/-- The actual adelic line parabolic subgroup. -/
abbrev Line := lineParabolic Adeles

/-- Actual ring maps preserve the true upper plane parabolic. -/
theorem inPlane_map {S : Type*} [CommRing S] (φ : R →+* S) (g : GL3 R)
    (hg : InPlaneParabolic g) : InPlaneParabolic (GeneralLinearGroup.map φ g) := by
  exact ⟨(congrArg φ hg.1).trans (map_zero φ), (congrArg φ hg.2).trans (map_zero φ)⟩

/-- Actual ring maps preserve the true upper line parabolic. -/
theorem inLine_map {S : Type*} [CommRing S] (φ : R →+* S) (g : GL3 R)
    (hg : InLineParabolic g) : InLineParabolic (GeneralLinearGroup.map φ g) := by
  exact ⟨(congrArg φ hg.1).trans (map_zero φ), (congrArg φ hg.2).trans (map_zero φ)⟩

end GeneralEisenstein.Adelic

end
