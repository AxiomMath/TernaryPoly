module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyTodd
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyAlgebra
public import TernaryPeriodPolynomials.AlternatingSolution.ToddLinearity

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.RadicalFirstCohomologyTodd
open RadicalCoinvariantAlgebra
open RadicalFirstCohomologyAlgebra (lineFlip finSuccEquiv_lineFlip)

/-- Reflection, with the inverse lattice translation, has the exact finite Todd intertwiner. -/
theorem todd_reflection {R : Type*} [CommRing R] [IsDomain R] [Algebra ℚ R]
    (u : R) (hu : u≠0) (p : Polynomial R) :
    todd u (p.comp (Polynomial.C u-Polynomial.X))=(todd u p).comp (-Polynomial.X) := by
  obtain ⟨q,hq⟩ := exists_taylor_sub_eq_mul u p
  have ht : (Polynomial.taylor (-u) q-q).comp (Polynomial.C u-Polynomial.X) =
      -(Polynomial.taylor (-u) (q.comp (-Polynomial.X))-q.comp (-Polynomial.X)) := by
    simp only [Polynomial.sub_comp,Polynomial.taylor_apply,Polynomial.comp_assoc,
      Polynomial.add_comp,Polynomial.sub_comp,Polynomial.neg_comp,
      Polynomial.X_comp,Polynomial.C_comp]
    have he : Polynomial.C u-Polynomial.X+Polynomial.C (-u)=(-Polynomial.X : Polynomial R) := by
      rw [map_neg]; ring
    have he' : -(Polynomial.X+Polynomial.C (-u))=(Polynomial.C u-Polynomial.X : Polynomial R) := by
      rw [map_neg]; ring
    rw [he,he']
    abel
  have he : todd u ((Polynomial.taylor (-u) q-q).comp (Polynomial.C u-Polynomial.X)) =
      (todd u (Polynomial.taylor (-u) q-q)).comp (-Polynomial.X) := by
    rw [ht,map_neg,todd_difference,todd_difference,Polynomial.derivative_comp]
    simp [Polynomial.smul_eq_C_mul]
  rw [hq,map_smul] at he
  simp only [Polynomial.smul_eq_C_mul,Polynomial.mul_comp,Polynomial.C_comp] at he
  rw [← Polynomial.smul_eq_C_mul,map_smul,Polynomial.smul_eq_C_mul] at he
  exact mul_left_cancel₀ (by simpa using hu : Polynomial.C u≠0) he

/-- The actual first-coordinate reflection intertwines Todd and a negative shear. -/
theorem firstTodd_lineFlip_shear (j : Fin 2) (p : Poly) :
    ternaryTodd (X j) (lineFlip p)=
      lineFlip (ternaryTodd (X j) (shear 0 j.succ p)) := by
  apply (finSuccEquiv ℚ 2).injective
  simp only [ternaryTodd,AlgEquiv.apply_symm_apply,finSuccEquiv_lineFlip,finSuccEquiv_shear]
  have h := todd_reflection (X j) (X_ne_zero j) (Polynomial.taylor (-X j) (finSuccEquiv ℚ 2 p))
  have he : (Polynomial.taylor (-X j) (finSuccEquiv ℚ 2 p)).comp
      (Polynomial.C (X j)-Polynomial.X) = (finSuccEquiv ℚ 2 p).comp (-Polynomial.X) := by
    rw [Polynomial.taylor_apply,Polynomial.comp_assoc]
    congr 1
    simp only [Polynomial.add_comp,Polynomial.X_comp,map_neg,Polynomial.neg_comp,Polynomial.C_comp]
    ring
  rwa [he] at h

/-- Todd commutes with both actual line-radical translations. -/
theorem firstTodd_shear (i j : Fin 2) (p : Poly) :
    ternaryTodd (X i) (shear 0 j.succ p)=shear 0 j.succ (ternaryTodd (X i) p) := by
  apply (finSuccEquiv ℚ 2).injective
  simp only [ternaryTodd,AlgEquiv.apply_symm_apply,finSuccEquiv_shear]
  exact (taylor_todd _ _ _).symm

/-- Todd commutes with the first partial derivative. -/
theorem firstTodd_pderiv (j : Fin 2) (p : Poly) :
    ternaryTodd (X j) (pderiv 0 p)=pderiv 0 (ternaryTodd (X j) p) := by
  apply (finSuccEquiv ℚ 2).injective
  simp only [ternaryTodd,AlgEquiv.apply_symm_apply,finSuccEquiv_pderiv_zero]
  exact (derivative_todd _ _).symm

/-- Both coefficient variables are scalars for both line Todd maps. -/
theorem firstTodd_X_mul (i j : Fin 2) (p : Poly) :
    ternaryTodd (X i) (X j.succ*p)=X j.succ*ternaryTodd (X i) p :=
  ternaryTodd_mul_of_coefficient (X i) (X j) _ p (finSuccEquiv_X_succ (R:=ℚ))

@[simp] theorem firstTodd_sub (j : Fin 2) (p q : Poly) :
    ternaryTodd (X j) (p-q)=ternaryTodd (X j) p-ternaryTodd (X j) q :=
  (firstToddLinear (X j)).map_sub p q

@[simp] theorem firstTodd_add (j : Fin 2) (p q : Poly) :
    ternaryTodd (X j) (p+q)=ternaryTodd (X j) p+ternaryTodd (X j) q :=
  (firstToddLinear (X j)).map_add p q

@[simp] theorem firstTodd_neg (j : Fin 2) (p : Poly) :
    ternaryTodd (X j) (-p)= -ternaryTodd (X j) p :=
  (firstToddLinear (X j)).map_neg p

theorem firstTodd_difference_poly (j : Fin 2) (p : Poly) :
    ternaryTodd (X j) (shear 0 j.succ p-p)= -(X j.succ)*pderiv 0 p := by
  apply (finSuccEquiv ℚ 2).injective
  simp only [ternaryTodd,AlgEquiv.apply_symm_apply,map_sub,finSuccEquiv_shear,
    map_mul,map_neg,finSuccEquiv_X_succ,finSuccEquiv_pderiv_zero]
  simpa only [map_sub,Polynomial.smul_eq_C_mul,map_neg] using
    todd_difference (X j) (finSuccEquiv ℚ 2 p)

/-- The explicit pair of line Todd maps takes the lattice cocycle equation to the root equation. -/
theorem lineTodd_closed (a b : Poly)
    (h : shear 0 1 b-b=shear 0 2 a-a) :
    (-X 1)*pderiv 0 (ternaryTodd (X (1 : Fin 2)) b)-
      (-X 2)*pderiv 0 (ternaryTodd (X (0 : Fin 2)) a)=0 := by
  have he := congrArg (fun p => ternaryTodd (X (0 : Fin 2))
    (ternaryTodd (X (1 : Fin 2)) p)) h
  have hs := firstTodd_shear 1 0 b
  have hd₀ := firstTodd_difference_poly 0 (ternaryTodd (X (1 : Fin 2)) b)
  have hd₁ := firstTodd_difference_poly 1 a
  have hx := firstTodd_X_mul 0 1 (pderiv 0 a)
  simp only [Fin.succ_zero_eq_one] at hs hd₀
  simp only [Fin.succ_one_eq_two] at hd₁ hx
  rw [firstTodd_sub,hs,hd₀,hd₁] at he
  simp only [neg_mul] at he
  rw [firstTodd_neg 0 (X 2*pderiv 0 a),hx,firstTodd_pderiv 0 a] at he
  exact sub_eq_zero.mpr (by simpa only [neg_mul] using he)

end TernaryPoly.RadicalFirstCohomologyTodd
