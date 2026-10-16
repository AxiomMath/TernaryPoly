module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLineTodd
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Naturality
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Parameter

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.RadicalFirstCohomologyTodd
open RadicalCoinvariantAlgebra
open RadicalFirstCohomologyAlgebra (planeFlip lineFlip)

/-- The second plane Todd map is the literal coordinate-swap conjugate. -/
def secondTodd (p : Poly) : Poly := S (ternaryTodd (X (1 : Fin 2)) (S p))

private def flipOne : Poly →ₐ[ℚ] Poly := bind₁ ![X 0,-X 1,X 2]
private def coefficientFlip : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ :=
  bind₁ ![-X 0,X 1]
private def coefficientShear : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ :=
  bind₁ ![X 0-X 1,X 1]

private theorem finSuccEquiv_flipOne (p : Poly) :
    finSuccEquiv ℚ 2 (flipOne p)=Polynomial.map coefficientFlip.toRingHom (finSuccEquiv ℚ 2 p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [flipOne,coefficientFlip,finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,hp]
    fin_cases i <;> simp [flipOne,coefficientFlip,finSuccEquiv_X_zero,
      finSuccEquiv_ternary_X_one,finSuccEquiv_ternary_X_two]

private theorem finSuccEquiv_shear_one (p : Poly) :
    finSuccEquiv ℚ 2 (shear 1 2 p)=Polynomial.map coefficientShear.toRingHom (finSuccEquiv ℚ 2 p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [shear,coefficientShear,finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,hp]
    fin_cases i <;> simp [coefficientShear,finSuccEquiv_X_zero,
      finSuccEquiv_ternary_X_one,finSuccEquiv_ternary_X_two]

private theorem firstTodd_flipOne (p : Poly) :
    ternaryTodd (X (1 : Fin 2)) (flipOne p)=flipOne (ternaryTodd (X (1 : Fin 2)) p) := by
  apply (finSuccEquiv ℚ 2).injective
  simp only [ternaryTodd,AlgEquiv.apply_symm_apply,finSuccEquiv_flipOne]
  simpa [coefficientFlip] using (map_todd coefficientFlip (X 1) (finSuccEquiv ℚ 2 p)).symm

/-- A plane Todd operator commutes with the other root translation. -/
theorem firstTodd_plane_shear (p : Poly) :
    ternaryTodd (X (1 : Fin 2)) (shear 1 2 p)=shear 1 2 (ternaryTodd (X (1 : Fin 2)) p) := by
  apply (finSuccEquiv ℚ 2).injective
  simp only [ternaryTodd,AlgEquiv.apply_symm_apply,finSuccEquiv_shear_one]
  simpa [coefficientShear] using (map_todd coefficientShear (X 1) (finSuccEquiv ℚ 2 p)).symm

/-- A plane Todd operator commutes with the other partial derivative. -/
theorem firstTodd_plane_pderiv (p : Poly) :
    ternaryTodd (X (1 : Fin 2)) (pderiv 1 p)=pderiv 1 (ternaryTodd (X (1 : Fin 2)) p) := by
  apply (finSuccEquiv ℚ 2).injective
  have hd (q : Poly) : finSuccEquiv ℚ 2 (pderiv 1 q)=
      coefficientPDeriv 0 (finSuccEquiv ℚ 2 q) := by
    simpa only [Fin.succ_zero_eq_one] using finSuccEquiv_pderiv_succ (0 : Fin 2) q
  rw [hd]
  simp only [ternaryTodd,AlgEquiv.apply_symm_apply]
  rw [hd]
  exact (coefficientPDeriv_todd_of_ne 0 1 (by decide) _).symm

private theorem S_shear_zero (p : Poly) : S (shear 0 2 p)=shear 1 2 (S p) := by
  have he : S.comp (shear 0 2)=(shear 1 2).comp S := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [S,AlgHom.comp_apply]
  exact DFunLike.congr_fun he p

private theorem S_shear_one (p : Poly) : S (shear 1 2 p)=shear 0 2 (S p) := by
  have he := congrArg S (S_shear_zero (S p))
  simpa only [S_S] using he.symm

private theorem S_planeFlip (p : Poly) : S (planeFlip p)=planeFlip (S p) := by
  have he : S.comp planeFlip=planeFlip.comp S := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [S,planeFlip,AlgHom.comp_apply]
  exact DFunLike.congr_fun he p

private theorem S_pderiv_one (p : Poly) : S (pderiv 1 p)=pderiv 0 (S p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [S]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    simp only [S] at hp
    fin_cases i <;> simp [S,map_mul,map_add,hp]

private theorem S_homogeneous {p : Poly} {n : ℕ} (hp : p.IsHomogeneous n) :
    (S p).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hp
  intro i
  fin_cases i <;> exact isHomogeneous_X ℚ _

/-- The literal second plane Todd map preserves exact degree. -/
theorem secondTodd_homogeneous {p : Poly} {n : ℕ} (hp : p.IsHomogeneous n) :
    (secondTodd p).IsHomogeneous n :=
  S_homogeneous (ternaryTodd_homogeneous (S_homogeneous hp) (isHomogeneous_X ℚ 1))

/-- The literal second plane Todd map is injective. -/
theorem secondTodd_injective : Function.Injective secondTodd := by
  intro p q h
  have he := congrArg S h
  simp only [secondTodd,S_S] at he
  have he' := ternaryTodd_injective (X (1 : Fin 2)) he
  simpa only [S_S] using congrArg S he'

@[simp] theorem secondTodd_sub (p q : Poly) : secondTodd (p-q)=secondTodd p-secondTodd q := by
  simp [secondTodd]

@[simp] theorem secondTodd_add (p q : Poly) : secondTodd (p+q)=secondTodd p+secondTodd q := by
  simp [secondTodd]

@[simp] theorem secondTodd_neg (p : Poly) : secondTodd (-p)= -secondTodd p := by
  simp [secondTodd]

/-- Second-coordinate differences become the actual negative dual root derivative. -/
theorem secondTodd_difference (p : Poly) :
    secondTodd (shear 1 2 p-p)=(-X 2)*pderiv 1 p := by
  have hd := firstTodd_difference_poly (1 : Fin 2) (S p)
  simp only [Fin.succ_one_eq_two] at hd
  unfold secondTodd
  rw [map_sub,S_shear_one,hd,map_mul,map_neg,←S_pderiv_one,S_S]
  simp [S]

/-- The second plane Todd map commutes with the first root translation. -/
theorem secondTodd_plane_shear (p : Poly) :
    secondTodd (shear 0 2 p)=shear 0 2 (secondTodd p) := by
  simp only [secondTodd,S_shear_zero,firstTodd_plane_shear,S_shear_one]

/-- Exact cross-root differentiation for the first plane Todd map. -/
theorem firstTodd_plane_root (p : Poly) :
    ternaryTodd (X (1 : Fin 2)) ((-X 2)*pderiv 1 p)=
      (-X 2)*pderiv 1 (ternaryTodd (X (1 : Fin 2)) p) := by
  have hx := firstTodd_X_mul (1 : Fin 2) (1 : Fin 2) (pderiv 1 p)
  simp only [Fin.succ_one_eq_two] at hx
  rw [neg_mul,firstTodd_neg,hx,firstTodd_plane_pderiv,neg_mul]

/-- The simultaneous plane reflection includes exactly the inverse first-root translation. -/
theorem firstTodd_planeFlip_shear (p : Poly) :
    ternaryTodd (X (1 : Fin 2)) (planeFlip p)=
      planeFlip (ternaryTodd (X (1 : Fin 2)) (shear 0 2 p)) := by
  have hf (q : Poly) : planeFlip q=flipOne (lineFlip q) := by
    have he : planeFlip=flipOne.comp lineFlip := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [planeFlip,flipOne,lineFlip,AlgHom.comp_apply]
    exact DFunLike.congr_fun he q
  rw [hf,firstTodd_flipOne,firstTodd_lineFlip_shear,hf]
  simp only [Fin.succ_one_eq_two]

/-- The second plane reflection has its exact inverse-root Todd intertwiner. -/
theorem secondTodd_planeFlip_shear (p : Poly) :
    secondTodd (planeFlip p)=planeFlip (secondTodd (shear 1 2 p)) := by
  simp only [secondTodd,S_planeFlip,firstTodd_planeFlip_shear,S_shear_one]

/-- Literal plane lattice cocycle closedness becomes the derivative closed-pair equation. -/
theorem planeTodd_closed (a b : Poly) (h : shear 0 2 b-b=shear 1 2 a-a) :
    (-X 2)*pderiv 0 (secondTodd b)-
      (-X 2)*pderiv 1 (ternaryTodd (X (1 : Fin 2)) a)=0 := by
  have he := congrArg (fun p => ternaryTodd (X (1 : Fin 2)) (secondTodd p)) h
  rw [secondTodd_sub,secondTodd_plane_shear] at he
  have hd := firstTodd_difference_poly (1 : Fin 2) (secondTodd b)
  simp only [Fin.succ_one_eq_two] at hd
  rw [hd,secondTodd_difference,firstTodd_plane_root] at he
  exact sub_eq_zero.mpr he

end TernaryPoly.RadicalFirstCohomologyTodd
