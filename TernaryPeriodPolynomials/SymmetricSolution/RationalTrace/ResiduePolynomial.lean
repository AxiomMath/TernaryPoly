module

public import TernaryPeriodPolynomials.SymmetricSolution.RationalTrace.SinglePole
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.CanonicalLift

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricRationalTrace
open SymmetricOddRationalSeed SymmetricOddRationalTower OrdinaryRationalFiber SinglePoleCoordinate

/-- The exact eight-term odd projector preserves homogeneous degree. -/
theorem oddProjection_homogeneous {n : ℕ} {f : TP} (hf : f.IsHomogeneous n) :
    (oddProjection f).IsHomogeneous n := by
  unfold oddProjection
  apply (homogeneousSubmodule (Fin 3) ℚ n).smul_mem
  have hx (i : Fin 3) := isHomogeneous_X ℚ i
  have h0 := substitute_homogeneous hf (hx 0) (hx 1) (hx 2)
  have h1 := substitute_homogeneous hf (hx 0) (hx 1) (hx 2).neg
  have h2 := substitute_homogeneous hf (hx 0) (hx 1).neg (hx 2)
  have h3 := substitute_homogeneous hf (hx 0) (hx 1).neg (hx 2).neg
  have h4 := substitute_homogeneous hf (hx 0).neg (hx 1) (hx 2)
  have h5 := substitute_homogeneous hf (hx 0).neg (hx 1) (hx 2).neg
  have h6 := substitute_homogeneous hf (hx 0).neg (hx 1).neg (hx 2)
  have h7 := substitute_homogeneous hf (hx 0).neg (hx 1).neg (hx 2).neg
  exact ((((((h0.sub h1).sub h2).add h3).sub h4).add h5).add h6).sub h7

theorem cyclicPolynomial_homogeneous {n : ℕ} {f : TP} (hf : f.IsHomogeneous n) :
    (cyclicPolynomial f).IsHomogeneous n := by
  have hc {p : TP} (hp : p.IsHomogeneous n) : (C p).IsHomogeneous n :=
    substitute_homogeneous hp (isHomogeneous_X ℚ 1) (isHomogeneous_X ℚ 2) (isHomogeneous_X ℚ 0)
  exact (hf.add (hc hf)).add (hc (hc hf))

variable {n k : ℕ}

theorem cyclicRegular_homogeneous (q : Fin k → BP)
    (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) :
    (cyclicRegular q).IsHomogeneous n := by
  have hh (i j l : Fin 3) : (regular q (X i) (X j) (X l)).IsHomogeneous n :=
    regular_homogeneous q hq hd (isHomogeneous_X ℚ i) (X_ne_zero i)
      (isHomogeneous_X ℚ j) (isHomogeneous_X ℚ l)
  exact ((hh 0 1 2).add (hh 1 2 0)).add (hh 2 0 1)

/-- The retained regular/Q/f correction has exactly the homogeneous degree. -/
theorem polynomialCorrection_homogeneous (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) :
    (polynomialCorrection f q hq).IsHomogeneous n := by
  simpa only [polynomialCorrection,map_ofNat] using
    (((cyclicRegular_homogeneous q hq hd).C_mul 2).add
      ((cyclicPolynomial_homogeneous (oddProjection_homogeneous (qPolynomial_homogeneous q hq hd))).C_mul 4)).add
        ((oddProjection_homogeneous hf).C_mul 8)

def lowestHomogeneous (q : Fin k → BP)
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) : BinaryV (n+1) :=
  ⟨lowest q,lowest_homogeneous q hd⟩

def correctionHomogeneous (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) : SinglePole.V n :=
  ⟨polynomialCorrection f q hq,polynomialCorrection_homogeneous f hf q hq hd⟩

/-- Exact equality inside the actual homogeneous single-pole module, including the polynomial part. -/
theorem homogeneousTrace_decomposition (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) :
    homogeneousTrace f hf q hq hd=
      (2 : ℚ) • canonicalRepresentative n (lowestHomogeneous q hd)+
        SinglePole.polynomialInclusion n (correctionHomogeneous f hf q hq hd) := by
  apply Subtype.ext
  simp only [homogeneousTrace_val,Submodule.coe_add,SetLike.val_smul,
    OrdinaryResidueGeneral.canonicalRepresentative_literal,SinglePole.polynomialInclusion_val]
  rw [rat_smul_eq_mul]
  simpa only [lowestHomogeneous,correctionHomogeneous,Rat.cast_ofNat] using trace_residue_correction f q hq

/-- Literal residues recover the common numerator of the homogeneous canonical representative. -/
theorem coordinateResidue_canonical (i : Fin 3) (q : BinaryV (n+1)) :
    coordinateResidue n i (canonicalRepresentative n q)=q := by
  rw [canonicalRepresentative,map_add,map_add]
  fin_cases i
  · change coordinateResidue n 0 (coordinatePole n 0 q)+coordinateResidue n 0 (coordinatePole n 1 q)+
      coordinateResidue n 0 (coordinatePole n 2 q)=q
    rw [coordinateResidue_coordinatePole n 0 q,
      coordinateResidue_coordinatePole_ne n 0 1 (by decide) q,
      coordinateResidue_coordinatePole_ne n 0 2 (by decide) q]
    simp only [add_zero]
  · change coordinateResidue n 1 (coordinatePole n 0 q)+coordinateResidue n 1 (coordinatePole n 1 q)+
      coordinateResidue n 1 (coordinatePole n 2 q)=q
    rw [coordinateResidue_coordinatePole_ne n 1 0 (by decide) q,
      coordinateResidue_coordinatePole n 1 q,
      coordinateResidue_coordinatePole_ne n 1 2 (by decide) q]
    simp only [zero_add,add_zero]
  · change coordinateResidue n 2 (coordinatePole n 0 q)+coordinateResidue n 2 (coordinatePole n 1 q)+
      coordinateResidue n 2 (coordinatePole n 2 q)=q
    rw [coordinateResidue_coordinatePole_ne n 2 0 (by decide) q,
      coordinateResidue_coordinatePole_ne n 2 1 (by decide) q,
      coordinateResidue_coordinatePole n 2 q]
    simp only [zero_add,add_zero]

/-- A literal fraction formula identifies its actual coordinate residue with its binary numerator. -/
theorem coordinateResidue_of_lift (x : SinglePole.singlePole n) (q : BinaryV (n+1))
    (p : SinglePole.V n)
    (hx : x.val=OrdinaryResiduePolynomial.representative q.val (X 0) (X 1) (X 2)+embed p.val)
    (i : Fin 3) : coordinateResidue n i x=q := by
  have he : x=canonicalRepresentative n q+SinglePole.polynomialInclusion n p := by
    apply Subtype.ext
    simpa only [Submodule.coe_add,OrdinaryResidueGeneral.canonicalRepresentative_literal,
      SinglePole.polynomialInclusion_val] using hx
  rw [he,map_add,coordinateResidue_canonical,coordinateResidue_polynomial,add_zero]

/-- All three actual literal coordinate residues are exactly twice the actual lowest tower period. -/
theorem coordinateResidue_homogeneousTrace (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) (i : Fin 3) :
    coordinateResidue n i (homogeneousTrace f hf q hq hd)=(2 : ℚ) • lowestHomogeneous q hd := by
  rw [homogeneousTrace_decomposition,map_add,map_smul,coordinateResidue_polynomial,add_zero,
    coordinateResidue_canonical]

/-- The literal binary-polynomial value is exactly twice the actual lowest period. -/
theorem coordinateResidue_homogeneousTrace_val (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) (i : Fin 3) :
    (coordinateResidue n i (homogeneousTrace f hf q hq hd)).val=2*lowest q := by
  have he := congrArg Subtype.val (coordinateResidue_homogeneousTrace f hf q hq hd i)
  simpa only [SetLike.val_smul,lowestHomogeneous,smul_eq_C_mul,map_ofNat] using he

end TernaryPoly.SymmetricRationalTrace
