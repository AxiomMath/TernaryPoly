module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ExplicitBinaryAction

@[expose] public section


/-!
# Linear (pair) cocycles of the bad-line radical and the rational Levi action

The radical `U ≅ ℤ²` of the bad-line stabilizer acts through `ρ_n = rationalCoefficientComponent n`
trivially on the image of the binary embedding `emb : Sym^n(ℂ²) → Sym^n(ℂ³)` (Sol's
`binaryHomogeneousEmbedding`), and the rational Levi elements `R(0, a, B)` act on it by
`emb P ↦ (a det B)⁻¹ emb(B · P)` (`rho_R_emb`). A pair `P = (P₁, P₂)` of binary polynomials gives the
linear cocycle `LP P (v) = v₁ emb P₁ + v₂ emb P₂`; the Levi blocks `B_j` of the Hecke cosets send it
to `LP (binaryMatrixPairAction B_j P)` (`levi_LP`), whose wedge coordinate is `ρ_{n+1}(B_j)` of the
wedge coordinate of `P` (Sol's `binaryPairWedge_matrixAction`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLinePairs

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open LineCoordinates IdentityPlaneCosets LevelOneCosets LevelThreeCosets BadLineCoordinates
open BadLineCosets BadLineTransitions IdentityPlaneCoordinate

/-! ### The Levi and radical elements in the coordinates `R` -/

theorem R_zero (a : ℚˣ) (B : GL (Fin 2) ℚ) : R 0 a B = lineLevi a B := by
  apply Units.ext
  rw [R_val, lineLevi_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vmul]

theorem R_unipotent (w : ℚ × ℚ) : R w 1 1 = lineUnipotent w.1 w.2 := by
  apply Units.ext
  rw [R_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lineUnipotent, upperUnipotent, vmul]

theorem R_factor (w : ℚ × ℚ) (a : ℚˣ) (B : GL (Fin 2) ℚ) : R w a B = R w 1 1 * R 0 a B := by
  rw [R_mul]
  refine R_congr ?_ ?_ ?_
  · simp [vmul_zero]
  · simp
  · simp

theorem Ux_eq_unipotent (x : ℤ × ℤ) :
    ((Ux x : ΛB) : RationalGL3) = lineUnipotent (x.1 : ℚ) (x.2 : ℚ) := by
  rw [Ux, Mel_val]
  have h := R_unipotent (icast x)
  refine Eq.trans ?_ h
  exact R_congr rfl (by simp) (by simp)

/-! ### The action on the binary embedding -/

section Action

variable (n : ℕ)

theorem rho_unipotent_emb (w : ℚ × ℚ) (P : Binary.HomogeneousPoly n) :
    ρn n (R w 1 1) (binaryHomogeneousEmbedding n P) = binaryHomogeneousEmbedding n P := by
  rw [R_unipotent]
  exact binaryHomogeneousEmbedding_lineUnipotent n w.1 w.2 P

theorem rho_Ux_emb (x : ℤ × ℤ) (P : Binary.HomogeneousPoly n) :
    ρn n ((Ux x : ΛB) : RationalGL3) (binaryHomogeneousEmbedding n P) =
      binaryHomogeneousEmbedding n P := by
  rw [Ux_eq_unipotent]
  exact binaryHomogeneousEmbedding_lineUnipotent n _ _ P

theorem rho_lineLevi_emb (a : ℚˣ) (B : GL (Fin 2) ℚ) (P : Binary.HomogeneousPoly n) :
    ρn n (lineLevi a B) (binaryHomogeneousEmbedding n P) =
      ((algebraMap ℚ ℂ (a : ℚ) * (GeneralLinearGroup.det (cx2 B)).val)⁻¹) •
        binaryHomogeneousEmbedding n (Binary.homogeneousAction n 0 (cx2 B) P) := by
  apply Subtype.ext
  rw [rho_coe, map_lineLevi]
  change action (-1) (lineLevi (Units.map (algebraMap ℚ ℂ).toMonoidHom a) (cx2 B))
    (binaryPolynomialEmbedding P.val) = _
  rw [action_lineLevi_binary]
  change _ = ((algebraMap ℚ ℂ (a : ℚ) * (GeneralLinearGroup.det (cx2 B)).val)⁻¹) •
    binaryPolynomialEmbedding (Binary.homogeneousAction n 0 (cx2 B) P).val
  rw [binaryUntwistedHomogeneous_val]
  rfl

/-- **The action of `R(w, a, B)` on the binary embedding.** -/
theorem rho_R_emb (w : ℚ × ℚ) (a : ℚˣ) (B : GL (Fin 2) ℚ) (P : Binary.HomogeneousPoly n) :
    ρn n (R w a B) (binaryHomogeneousEmbedding n P) =
      ((algebraMap ℚ ℂ (a : ℚ) * (GeneralLinearGroup.det (cx2 B)).val)⁻¹) •
        binaryHomogeneousEmbedding n (Binary.homogeneousAction n 0 (cx2 B) P) := by
  rw [R_factor, map_mul, Module.End.mul_apply, R_zero, rho_lineLevi_emb, map_smul,
    rho_unipotent_emb]

/-- The scalar case `B = 1`. -/
theorem rho_R_one_emb (w : ℚ × ℚ) (a : ℚˣ) (P : Binary.HomogeneousPoly n) :
    ρn n (R w a 1) (binaryHomogeneousEmbedding n P) =
      (algebraMap ℚ ℂ (a : ℚ))⁻¹ • binaryHomogeneousEmbedding n P := by
  rw [rho_R_emb]
  simp

/-! ### Linear cocycles -/

/-- The linear cochain `v ↦ v₁ emb P₁ + v₂ emb P₂`. -/
def LP (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (v : ℤ × ℤ) :
    HomogeneousPoly n :=
  (v.1 : ℂ) • binaryHomogeneousEmbedding n P.1 + (v.2 : ℂ) • binaryHomogeneousEmbedding n P.2

theorem LP_add (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (v w : ℤ × ℤ) :
    LP n P (v + w) = LP n P v + LP n P w := by
  simp only [LP, Prod.fst_add, Prod.snd_add, Int.cast_add, add_smul]
  abel

theorem LP_smul (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (z : ℤ) (v : ℤ × ℤ) :
    LP n P (z • v) = (z : ℂ) • LP n P v := by
  simp only [LP, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Int.cast_mul, mul_smul, smul_add]

/-- `LP` as an additive homomorphism. -/
def LPh (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) :
    (ℤ × ℤ) →+ HomogeneousPoly n :=
  AddMonoidHom.mk' (LP n P) (LP_add n P)

theorem LP_sum {ι : Type*} (s : Finset ι) (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n)
    (f : ι → ℤ × ℤ) : LP n P (∑ i ∈ s, f i) = ∑ i ∈ s, LP n P (f i) :=
  map_sum (LPh n P) f s

/-- `LP` as a linear function of the pair. -/
def LPlin (v : ℤ × ℤ) :
    (Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) →ₗ[ℂ] HomogeneousPoly n :=
  (v.1 : ℂ) • (binaryHomogeneousEmbedding n).comp (LinearMap.fst ℂ _ _) +
    (v.2 : ℂ) • (binaryHomogeneousEmbedding n).comp (LinearMap.snd ℂ _ _)

theorem LP_eq_lin (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (v : ℤ × ℤ) :
    LP n P v = LPlin n v P := by
  simp [LP, LPlin]

theorem LP_pair_add (P Q : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (v : ℤ × ℤ) :
    LP n (P + Q) v = LP n P v + LP n Q v := by
  rw [LP_eq_lin, LP_eq_lin, LP_eq_lin, map_add]

theorem LP_pair_sum {ι : Type*} (s : Finset ι)
    (P : ι → Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (v : ℤ × ℤ) :
    LP n (∑ i ∈ s, P i) v = ∑ i ∈ s, LP n (P i) v := by
  simp only [LP_eq_lin]
  exact map_sum (LPlin n v) P s

theorem LP_pair_smul (c : ℂ) (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n)
    (v : ℤ × ℤ) : LP n (c • P) v = c • LP n P v := by
  rw [LP_eq_lin, LP_eq_lin, map_smul]

theorem cx2_BQ (p : Nat.Primes) (j : Option (Fin p.val)) :
    (cx2 (BQ p j)).val = (Bl p j).map (Int.cast : ℤ → ℂ) := by
  ext a b
  simp [cx2, BQ_val, GeneralLinearGroup.map_apply]

/-- **The Levi blocks send linear cocycles to linear cocycles.** -/
theorem levi_LP (p : Nat.Primes) (j : Option (Fin p.val))
    (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (r : ℤ × ℤ) :
    ρn n (sLev p j) (LP n P (ivmul r (Bl p j))) =
      LP n (binaryMatrixPairAction n (cx2 (BQ p j)) P) r := by
  have hs : ∀ Q : Binary.HomogeneousPoly n, ρn n (sLev p j) (binaryHomogeneousEmbedding n Q) =
      ((GeneralLinearGroup.det (cx2 (BQ p j))).val)⁻¹ •
        binaryHomogeneousEmbedding n (Binary.homogeneousAction n 0 (cx2 (BQ p j)) Q) := by
    intro Q
    rw [sLev, rho_R_emb]
    simp
  have e1 : (cx2 (BQ p j)).val 0 0 = ((Bl p j 0 0 : ℤ) : ℂ) := by rw [cx2_BQ]; rfl
  have e2 : (cx2 (BQ p j)).val 0 1 = ((Bl p j 0 1 : ℤ) : ℂ) := by rw [cx2_BQ]; rfl
  have e3 : (cx2 (BQ p j)).val 1 0 = ((Bl p j 1 0 : ℤ) : ℂ) := by rw [cx2_BQ]; rfl
  have e4 : (cx2 (BQ p j)).val 1 1 = ((Bl p j 1 1 : ℤ) : ℂ) := by rw [cx2_BQ]; rfl
  simp only [LP, ivmul, map_add, map_smul, hs, binaryMatrixPairAction, e1, e2, e3, e4]
  push_cast
  module

end Action

end TernaryPeriodPolynomials.LevelThree.BadLinePairs
