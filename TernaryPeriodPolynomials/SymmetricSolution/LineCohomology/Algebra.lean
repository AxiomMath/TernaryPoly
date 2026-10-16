module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLineComparison
public import TernaryPeriodPolynomials.GroupCohomology.Radical.ToddSurjective

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricLineCohomology
open RadicalCoinvariantAlgebra RadicalFirstCohomology
open RadicalFirstCohomologyAlgebra (line_coordinate_closed line_coordinate_exact)

abbrev BP := MvPolynomial (Fin 2) ℚ

def binaryRestrict : Poly →ₐ[ℚ] BP := bind₁ ![0, X 0, X 1]

@[simp] theorem binaryRestrict_rename (J : BP) :
    binaryRestrict (rename Fin.succ J) = J := by
  have h : binaryRestrict.comp (rename (Fin.succ : Fin 2 → Fin 3)) = AlgHom.id ℚ BP := by
    ext i
    fin_cases i <;> simp [binaryRestrict]
  exact DFunLike.congr_fun h J

/-- The literal last-two-coordinate retraction recovers every X-independent polynomial. -/
theorem rename_binaryRestrict {p : Poly} (hp : pderiv 0 p = 0) :
    rename Fin.succ (binaryRestrict p) = p := by
  have hd := congrArg (finSuccEquiv ℚ 2) hp
  rw [finSuccEquiv_pderiv_zero, map_zero] at hd
  have hc := Polynomial.eq_C_of_derivative_eq_zero hd
  let J := (finSuccEquiv ℚ 2 p).coeff 0
  have he : p = rename Fin.succ J := by
    apply (finSuccEquiv ℚ 2).injective
    rw [finSuccEquiv_rename_succ]
    exact hc
  rw [he, binaryRestrict_rename]

theorem binaryRestrict_homogeneous {p : Poly} {n : ℕ} (hp : p.IsHomogeneous n) :
    (binaryRestrict p).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hp
  intro i
  fin_cases i
  · exact isHomogeneous_zero _ _ _
  · exact isHomogeneous_X ℚ 0
  · exact isHomogeneous_X ℚ 1

/-- The positive determinant contraction of a derivative pair. -/
def contraction (n : ℕ) : (Fin 2 → H n) →ₗ[ℚ] Poly where
  toFun v := X 2 * (v 0 : Poly) - X 1 * (v 1 : Poly)
  map_add' a b := by simp only [Pi.add_apply, Submodule.coe_add]; ring
  map_smul' r a := by
    simp only [Pi.smul_apply, Submodule.coe_smul_of_tower, RingHom.id_apply]
    simp only [mul_smul_comm, smul_sub]

@[simp] theorem contraction_apply (n : ℕ) (v : Fin 2 → H n) :
    contraction n v = X 2 * (v 0 : Poly) - X 1 * (v 1 : Poly) := rfl

theorem contraction_homogeneous (n : ℕ) (v : Fin 2 → H n) :
    (contraction n v).IsHomogeneous (n+1) := by
  change (X 2 * (v 0 : Poly) - X 1 * (v 1 : Poly)).IsHomogeneous (n+1)
  simpa only [Nat.add_comm] using
    (((isHomogeneous_X ℚ 2).mul (v 0).property).sub
      ((isHomogeneous_X ℚ 1).mul (v 1).property))

theorem contraction_independent (n : ℕ) (v : lineDerivativeClosedPairs n) :
    pderiv 0 (contraction n v) = 0 := by
  apply line_coordinate_closed
  have h := congrArg Subtype.val v.property
  simpa only [lineDerivativeCurl_coe, ZeroMemClass.coe_zero] using h

/-- The complete binary scalar of a homogeneous closed derivative pair. -/
def scalar (n : ℕ) : lineDerivativeClosedPairs n →ₗ[ℚ] BinaryH (n+1) where
  toFun v := ⟨binaryRestrict (contraction n v),
    binaryRestrict_homogeneous (contraction_homogeneous n v)⟩
  map_add' a b := Subtype.ext (by change binaryRestrict (contraction n (a+b)) = _; simp only [Submodule.coe_add,map_add])
  map_smul' r a := Subtype.ext (by change binaryRestrict (contraction n (r • a)) = _; simp only [Submodule.coe_smul_of_tower,map_smul,RingHom.id_apply])

@[simp] theorem scalar_coe (n : ℕ) (v : lineDerivativeClosedPairs n) :
    (scalar n v : BP) = binaryRestrict (contraction n v) := rfl

@[simp] theorem scalar_rename (n : ℕ) (v : lineDerivativeClosedPairs n) :
    rename Fin.succ (scalar n v : BP) = contraction n v :=
  rename_binaryRestrict (contraction_independent n v)

theorem scalar_kernel (n : ℕ) (v : lineDerivativeClosedPairs n) :
    scalar n v = 0 ↔ ∃ g : H n, lineCommonDerivative n g = v := by
  constructor
  · intro h
    have hc : contraction n v = 0 := by
      rw [← scalar_rename, h, ZeroMemClass.coe_zero, map_zero]
    obtain ⟨g, hg, h0, h1⟩ := line_coordinate_exact (v.val 0).property hc
    refine ⟨⟨g,hg⟩, ?_⟩
    apply Subtype.ext
    funext j
    apply Subtype.ext
    change (lineDerivativePair n ⟨g,hg⟩ j : Poly) = _
    rw [lineDerivativePair_apply, lineRootDerivative_coe]
    fin_cases j
    · exact h0
    · exact h1
  · rintro ⟨g,rfl⟩
    apply Subtype.ext
    change binaryRestrict (contraction n (lineDerivativePair n g)) = 0
    have h : contraction n (lineDerivativePair n g) = 0 := by
      change X 2 * (lineDerivativePair n g 0 : Poly) -
        X 1 * (lineDerivativePair n g 1 : Poly) = 0
      rw [lineDerivativePair_apply, lineDerivativePair_apply,
        lineRootDerivative_coe, lineRootDerivative_coe]
      simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
      ring
    rw [h,map_zero]

/-- Euler's section as an actual homogeneous closed derivative pair. -/
def eulerPair (n : ℕ) (J : BinaryH (n+1)) : lineDerivativeClosedPairs n :=
  ⟨![⟨radicalEulerFirst (n+1) J, by simpa using (radicalEuler_homogeneous J.property).1⟩,
     ⟨radicalEulerSecond (n+1) J, by simpa using (radicalEuler_homogeneous J.property).2⟩], by
    apply Subtype.ext
    rw [lineDerivativeCurl_coe]
    change (-X 1)*pderiv 0 (radicalEulerSecond (n+1) J)-
      (-X 2)*pderiv 0 (radicalEulerFirst (n+1) J)=0
    rw [(radicalEuler_independent _ _).1,(radicalEuler_independent _ _).2]
    simp⟩

@[simp] theorem eulerPair_first (n : ℕ) (J : BinaryH (n+1)) :
    ((eulerPair n J).val 0 : Poly) = radicalEulerFirst (n+1) J := rfl

@[simp] theorem eulerPair_second (n : ℕ) (J : BinaryH (n+1)) :
    ((eulerPair n J).val 1 : Poly) = radicalEulerSecond (n+1) J := rfl

@[simp] theorem scalar_eulerPair (n : ℕ) (J : BinaryH (n+1)) :
    scalar n (eulerPair n J) = J := by
  apply Subtype.ext
  rw [scalar_coe]
  rw [contraction_apply,eulerPair_first,eulerPair_second]
  have h := radicalEuler_todd_contraction (Nat.succ_pos n) J.property
  simp only [radicalEulerFirst,radicalEulerSecond,ternaryTodd_rename_succ] at h ⊢
  rw [h,binaryRestrict_rename]

theorem scalar_surjective (n : ℕ) : Function.Surjective (scalar n) :=
  fun J => ⟨eulerPair n J, scalar_eulerPair n J⟩

end TernaryPoly.SymmetricLineCohomology
