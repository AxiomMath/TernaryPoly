module

public import TernaryPeriodPolynomials.SymmetricSolution.LineCohomology.Algebra
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLine

@[expose] public section

open CategoryTheory MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricLineCohomology
open RadicalCoinvariantAlgebra RadicalFirstCohomology RadicalFirstCohomologyTodd
open LatticeTopCohomology LatticeFirstCohomology RadicalFirstCohomologyLattice
open groupCohomology

/-- Todd conversion of the two literal generator values of an actual crossed homomorphism. -/
def cocyclePair (n : ℕ) : cocycles₁ (lineRep n) →ₗ[ℚ] lineDerivativeClosedPairs n where
  toFun c := ⟨![firstTodd n 0 (c first), firstTodd n 1 (c second)], by
    apply Subtype.ext
    rw [lineDerivativeCurl_coe]
    exact lineTodd_closed _ _ (line_cocycle_closed n c)⟩
  map_add' c d := by
    apply Subtype.ext
    funext j
    fin_cases j <;> exact (firstTodd n _).map_add _ _
  map_smul' r c := by
    apply Subtype.ext
    funext j
    fin_cases j <;> exact (firstTodd n _).map_smul r _

/-- The binary scalar is defined directly on genuine group cocycles. -/
def cocycleScalar (n : ℕ) : cocycles₁ (lineRep n) →ₗ[ℚ] BinaryH (n+1) :=
  (scalar n).comp (cocyclePair n)

@[simp] theorem cocycleScalar_rename (n : ℕ) (c : cocycles₁ (lineRep n)) :
    rename Fin.succ (cocycleScalar n c : BP) =
      X 2 * ternaryTodd (X (0 : Fin 2)) (c first : Poly) -
      X 1 * ternaryTodd (X (1 : Fin 2)) (c second : Poly) :=
  scalar_rename n (cocyclePair n c)

theorem cocyclePair_coboundary (n : ℕ) (v : H n) :
    cocyclePair n (coboundary (lineRep n) v) = lineCommonDerivative n v := by
  apply Subtype.ext
  funext j
  fin_cases j
  · change firstTodd n 0 ((lineRep n).ρ first v-v) = lineDerivativePair n v 0
    rw [lineRep_first,lineDerivativePair_apply]
    rfl
  · change firstTodd n 1 ((lineRep n).ρ second v-v) = lineDerivativePair n v 1
    rw [lineRep_second,lineDerivativePair_apply]
    rfl

/-- The scalar detects exactly the genuine coboundaries, degree by degree. -/
theorem cocycleScalar_eq_zero_iff (n : ℕ) (c : cocycles₁ (lineRep n)) :
    cocycleScalar n c = 0 ↔ H1π (lineRep n) c = 0 := by
  rw [H1π_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨v,hv⟩ := (scalar_kernel n (cocyclePair n c)).mp h
    have he : c = coboundary (lineRep n) v := by
      apply cocycle_eq_of_generators
      · apply firstTodd_injective n 0
        exact congrArg (fun p : lineDerivativeClosedPairs n => p.val 0)
          (hv.symm.trans (cocyclePair_coboundary n v).symm)
      · apply firstTodd_injective n 1
        exact congrArg (fun p : lineDerivativeClosedPairs n => p.val 1)
          (hv.symm.trans (cocyclePair_coboundary n v).symm)
    rw [he]
    exact ⟨v,rfl⟩
  · rintro ⟨v,hv⟩
    have he : c = coboundary (lineRep n) v := by
      apply cocycles₁_ext
      intro g
      exact (congrFun hv g).symm
    change scalar n (cocyclePair n c)=0
    rw [he,cocyclePair_coboundary]
    exact (scalar_kernel n _).mpr ⟨v,rfl⟩

/-- Generatorwise invariance is full lattice invariance. -/
theorem fixed_of_generators (n : ℕ) (v : H n)
    (h0 : (lineRep n).ρ first v=v) (h1 : (lineRep n).ρ second v=v)
    (g : Lattice) : (lineRep n).ρ g v=v := by
  have h := cocycle_eq_zero_of_generators (lineRep n) (coboundary (lineRep n) v)
    (sub_eq_zero.mpr h0) (sub_eq_zero.mpr h1)
  exact sub_eq_zero.mp (congrArg (fun c : cocycles₁ (lineRep n) => c g) h)

theorem shear_rename_succ (j : Fin 2) (p : BP) :
    shear 0 j.succ (rename Fin.succ p) = rename Fin.succ p := by
  have he : shear 0 j.succ = alternatingShift (X j.succ) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> fin_cases j <;> simp [shear,alternatingShift]
  rw [he,alternatingShift_rename_succ]

/-- The Euler section is fixed by every actual radical element. -/
theorem eulerPair_fixed (n : ℕ) (J : BinaryH (n+1)) (j : Fin 2) (g : Lattice) :
    (lineRep n).ρ g ((eulerPair n J).val j) = (eulerPair n J).val j := by
  apply fixed_of_generators
  · rw [lineRep_first]
    apply Subtype.ext
    fin_cases j <;> exact shear_rename_succ 0 _
  · rw [lineRep_second]
    apply Subtype.ext
    fin_cases j <;> exact shear_rename_succ 1 _

/-- The Euler section extends to the literal additive cocycle of the integral lattice. -/
def eulerCocycle (n : ℕ) (J : BinaryH (n+1)) : cocycles₁ (lineRep n) :=
  ⟨fun g => g.toAdd.1 • (eulerPair n J).val 0 + g.toAdd.2 • (eulerPair n J).val 1, by
    apply (mem_cocycles₁_iff _).mpr
    intro g h
    change (g.toAdd.1+h.toAdd.1) • (eulerPair n J).val 0 +
      (g.toAdd.2+h.toAdd.2) • (eulerPair n J).val 1 = _
    rw [map_add,map_zsmul,map_zsmul,eulerPair_fixed,eulerPair_fixed]
    simp only [add_zsmul]
    abel⟩

@[simp] theorem eulerCocycle_first (n : ℕ) (J : BinaryH (n+1)) :
    eulerCocycle n J first = (eulerPair n J).val 0 := by
  change (1 : ℤ) • (eulerPair n J).val 0 + (0 : ℤ) • (eulerPair n J).val 1 = _
  simp

@[simp] theorem eulerCocycle_second (n : ℕ) (J : BinaryH (n+1)) :
    eulerCocycle n J second = (eulerPair n J).val 1 := by
  change (0 : ℤ) • (eulerPair n J).val 0 + (1 : ℤ) • (eulerPair n J).val 1 = _
  simp

@[simp] theorem cocyclePair_eulerCocycle (n : ℕ) (J : BinaryH (n+1)) :
    cocyclePair n (eulerCocycle n J) = eulerPair n J := by
  apply Subtype.ext
  funext j
  apply Subtype.ext
  fin_cases j
  · change ternaryTodd (X (0 : Fin 2)) (eulerCocycle n J first : Poly) = _
    rw [eulerCocycle_first]
    exact ternaryTodd_rename_succ _ _
  · change ternaryTodd (X (1 : Fin 2)) (eulerCocycle n J second : Poly) = _
    rw [eulerCocycle_second]
    exact ternaryTodd_rename_succ _ _

@[simp] theorem cocycleScalar_eulerCocycle (n : ℕ) (J : BinaryH (n+1)) :
    cocycleScalar n (eulerCocycle n J) = J := by
  change scalar n (cocyclePair n (eulerCocycle n J))=J
  rw [cocyclePair_eulerCocycle,scalar_eulerPair]

theorem cocycleScalar_surjective (n : ℕ) : Function.Surjective (cocycleScalar n) :=
  fun J => ⟨eulerCocycle n J,cocycleScalar_eulerCocycle n J⟩

/-- The kernels coincide as actual linear submodules of the genuine cocycle space. -/
theorem cocycleScalar_ker (n : ℕ) :
    LinearMap.ker (H1π (lineRep n)).hom = LinearMap.ker (cocycleScalar n) := by
  ext c
  exact (cocycleScalar_eq_zero_iff n c).symm

theorem H1π_surjective (n : ℕ) : Function.Surjective (H1π (lineRep n)) :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- Actual H¹ as the quotient by the kernel of its genuine cocycle projection. -/
def h1QuotientEquiv (n : ℕ) :=
  (H1π (lineRep n)).hom.quotKerEquivOfSurjective (H1π_surjective n)

/-- Descending the literal scalar through the genuine H¹ projection. -/
def latticeH1Scalar (n : ℕ) :
    groupCohomology (lineRep n) 1 →ₗ[ℚ] BinaryH (n+1) :=
  ((LinearMap.ker (H1π (lineRep n)).hom).liftQ (cocycleScalar n)
    (cocycleScalar_ker n).le).comp (h1QuotientEquiv n).symm.toLinearMap

@[simp] theorem latticeH1Scalar_H1π (n : ℕ) (c : cocycles₁ (lineRep n)) :
    latticeH1Scalar n (H1π (lineRep n) c) = cocycleScalar n c := by
  simp [latticeH1Scalar,h1QuotientEquiv]

theorem latticeH1Scalar_injective (n : ℕ) : Function.Injective (latticeH1Scalar n) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  change latticeH1Scalar n x = 0 at hx
  revert hx
  refine H1_induction_on x ?_
  intro c hc
  rw [latticeH1Scalar_H1π] at hc
  exact (cocycleScalar_eq_zero_iff n c).mp hc

theorem latticeH1Scalar_surjective (n : ℕ) : Function.Surjective (latticeH1Scalar n) := by
  intro J
  refine ⟨H1π (lineRep n) (eulerCocycle n J),?_⟩
  rw [latticeH1Scalar_H1π,cocycleScalar_eulerCocycle]

/-- Literal complete scalar coordinates on the actual first group cohomology. -/
def latticeH1ScalarEquiv (n : ℕ) :
    groupCohomology (lineRep n) 1 ≃ₗ[ℚ] BinaryH (n+1) :=
  LinearEquiv.ofBijective (latticeH1Scalar n)
    ⟨latticeH1Scalar_injective n,latticeH1Scalar_surjective n⟩

@[simp] theorem latticeH1ScalarEquiv_H1π (n : ℕ) (c : cocycles₁ (lineRep n)) :
    latticeH1ScalarEquiv n (H1π (lineRep n) c) = cocycleScalar n c :=
  latticeH1Scalar_H1π n c

/-- Every class is represented by the explicit Euler cocycle of its complete scalar. -/
theorem H1π_eulerCocycle_scalar (n : ℕ) (x : groupCohomology (lineRep n) 1) :
    H1π (lineRep n) (eulerCocycle n (latticeH1ScalarEquiv n x)) = x := by
  apply (latticeH1ScalarEquiv n).injective
  rw [latticeH1ScalarEquiv_H1π,cocycleScalar_eulerCocycle]

end TernaryPoly.SymmetricLineCohomology
