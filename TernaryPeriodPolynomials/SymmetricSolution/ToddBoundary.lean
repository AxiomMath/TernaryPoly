module

public import TernaryPeriodPolynomials.SymmetricSolution.Todd
public import TernaryPeriodPolynomials.SymmetricSolution.Boundary
public import TernaryPeriodPolynomials.AlternatingSolution.ToddLinearity
public import TernaryPeriodPolynomials.AlternatingSolution.ToddPlane

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- Multiplication by the coordinate sum acts through the common frame sum. -/
theorem symmetricFrame1_W_pow_mul (r : ℕ) (f : TernaryPolynomial) :
    symmetricFrame1 ((X 0+X 1+X 2)^r*f) =
      (X 2-3*X 1)^r*symmetricFrame1 f :=
  alternatingFrame1_W_pow_mul r f

theorem symmetricFrame2_W_pow_mul (r : ℕ) (f : TernaryPolynomial) :
    symmetricFrame2 ((X 0+X 1+X 2)^r*f) =
      (X 2-3*X 1)^r*symmetricFrame2 f := by
  have hsum2 : (X 2-X 0)+(X 0-2*X 1)+(-X 1) =
      (X 2-3*X 1 : TernaryPolynomial) := by ring
  have hsum3 : (X 2-2*X 1)+(X 1-X 0)+(X 0-2*X 1) =
      (X 2-3*X 1 : TernaryPolynomial) := by ring
  simp only [symmetricFrame2,symmetricFrame1_W_pow_mul,
    substitute3_W_pow_mul,hsum2,hsum3]
  ring

theorem symmetricTodd_W_pow_mul (r : ℕ) (f : TernaryPolynomial) :
    symmetricTodd ((X 0+X 1+X 2)^r*f) =
      (X 2-3*X 1)^r*symmetricTodd f := by
  simp only [symmetricTodd,symmetricFrame1_W_pow_mul,
    symmetricFrame2_W_pow_mul,ternaryTodd_Z_sub_three_Y_pow_mul]
  ring

/-- The lower cusp specialization, keeping the differentiation variable intact. -/
def toddAxisY : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial := bind₁ ![X 0,0,X 2]
def toddAxisYCoeff : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ :=
  bind₁ ![0,X 1]

theorem finSuccEquiv_toddAxisY (f : TernaryPolynomial) :
    finSuccEquiv ℚ 2 (toddAxisY f) =
      Polynomial.map toddAxisYCoeff.toRingHom (finSuccEquiv ℚ 2 f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [toddAxisY,toddAxisYCoeff,finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add,hp,hq,Polynomial.map_add]
  | mul_X p i hp =>
    simp only [map_mul,Polynomial.map_mul,hp]
    fin_cases i <;> simp [toddAxisY,toddAxisYCoeff,finSuccEquiv_X_zero,
      finSuccEquiv_ternary_X_one,finSuccEquiv_ternary_X_two]

theorem finSuccEquiv_toddAxisY_ternaryTodd (u : MvPolynomial (Fin 2) ℚ)
    (f : TernaryPolynomial) :
    finSuccEquiv ℚ 2 (toddAxisY (ternaryTodd u f)) =
      todd (toddAxisYCoeff u) (finSuccEquiv ℚ 2 (toddAxisY f)) := by
  rw [finSuccEquiv_toddAxisY,ternaryTodd,AlgEquiv.apply_symm_apply,
    map_todd,←finSuccEquiv_toddAxisY]

/-- The complete first frame vanishes at the lower cusp. -/
theorem symmetricFrame1_axisY {f : TernaryPolynomial} {n : ℕ}
    (hf : PeriodRelations f) (hs : S f=f) (hg : f.IsHomogeneous n) :
    toddAxisY (symmetricFrame1 f) = 0 := by
  have he : toddAxisY (symmetricFrame1 f) = substitute3 f (X 2) (-X 0) (X 0) := by
    change substitute3 (substitute3 f (X 2-2*X 1) (-X 0) (X 0-X 1))
      (X 0) 0 (X 2) = _
    rw [substitute3_substitute3]
    simp [substitute3]
  rw [he,←substitute3_cyclic hf.1 (X 2) (-X 0) (X 0)]
  simpa only [SymmetricCertificate.value,substitute3,neg_neg] using
    (symmetric_opposite_value_zero hf hs ((-1:ℚ)^n)
      (pow_ne_zero n (by norm_num)) (homogeneous_bind_neg hg) (-X 0) (X 2))

/-- The entire symmetric Todd scalar vanishes at Y=0 in every homogeneous degree. -/
theorem symmetricTodd_axisY {f : TernaryPolynomial} {n : ℕ}
    (hf : PeriodRelations f) (hs : S f=f) (hg : f.IsHomogeneous n) :
    toddAxisY (symmetricTodd f) = 0 := by
  have ht : toddAxisY (ternaryTodd (X (0:Fin 2)) (symmetricFrame1 f)) = 0 := by
    apply (finSuccEquiv ℚ 2).injective
    rw [finSuccEquiv_toddAxisY_ternaryTodd,symmetricFrame1_axisY hf hs hg]
    simp
  simp only [symmetricTodd,map_sub,map_mul,ht]
  simp [toddAxisY]

/-- All three symmetric frames vanish on the normal plane in even homogeneous degree. -/
theorem symmetric_frames_normalPlane {f : TernaryPolynomial} {n : ℕ}
    (hf : PeriodRelations f) (hs : S f=f) (hg : f.IsHomogeneous n) (hn : Even n) :
    normalPlane (symmetricFrame1 f) = 0 ∧ normalPlane (symmetricFrame2 f) = 0 := by
  have hv (a b : TernaryPolynomial) : substitute3 f a b (-(a+b))=0 :=
    symmetric_total_value_zero hf hs (homogeneous_bind_neg_even hg hn) a b
  have h1 : normalPlane (symmetricFrame1 f) = 0 := by
    have h := hv (X 1) (-X 0)
    change substitute3 (substitute3 f (X 2-2*X 1) (-X 0) (X 0-X 1)) (X 0) (X 1) (3*X 1) = 0
    rw [substitute3_substitute3]
    simp only [substitute3, map_sub, map_mul, map_ofNat, map_neg, bind₁_X_right,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    change substitute3 f _ _ _ = 0
    convert h using 1
    congr 1 <;> ring
  have h2 : normalPlane (substitute3 f (X 2-X 0) (X 0-2*X 1) (-X 1)) = 0 := by
    have h := hv (3*X 1-X 0) (X 0-2*X 1)
    change substitute3 (substitute3 f (X 2-X 0) (X 0-2*X 1) (-X 1)) (X 0) (X 1) (3*X 1) = 0
    rw [substitute3_substitute3]
    simp only [substitute3, map_sub, map_mul, map_ofNat, map_neg, bind₁_X_right,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    change substitute3 f _ _ _ = 0
    convert h using 1
    congr 1
    ring
  have h3 : normalPlane (substitute3 f (X 2-2*X 1) (X 1-X 0) (X 0-2*X 1)) = 0 := by
    have h := hv (X 1) (X 1-X 0)
    change substitute3 (substitute3 f (X 2-2*X 1) (X 1-X 0) (X 0-2*X 1)) (X 0) (X 1) (3*X 1) = 0
    rw [substitute3_substitute3]
    simp only [substitute3, map_sub, map_mul, map_ofNat, bind₁_X_right,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    change substitute3 f _ _ _ = 0
    convert h using 1
    congr 1 <;> ring
  exact ⟨h1, by simp only [symmetricFrame2,map_add,map_sub,h1,h2,h3,sub_self,add_zero]⟩

/-- The second cusp restriction of the entire scalar vanishes in even degree. -/
theorem symmetricTodd_normalPlane {f : TernaryPolynomial} {n : ℕ}
    (hf : PeriodRelations f) (hs : S f=f) (hg : f.IsHomogeneous n) (hn : Even n) :
    normalPlane (symmetricTodd f) = 0 := by
  obtain ⟨h1,h2⟩ := symmetric_frames_normalPlane hf hs hg hn
  have ht (u : MvPolynomial (Fin 2) ℚ) (g : TernaryPolynomial) (h : normalPlane g=0) :
      normalPlane (ternaryTodd u g)=0 := by
    apply (finSuccEquiv ℚ 2).injective
    rw [finSuccEquiv_normalPlane_ternaryTodd,h]
    simp
  simp only [symmetricTodd,map_sub,map_mul,ht _ _ h1,ht _ _ h2,mul_zero,sub_self]

end TernaryPoly
