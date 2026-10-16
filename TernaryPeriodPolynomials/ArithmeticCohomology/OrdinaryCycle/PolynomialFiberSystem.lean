module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.SignedFibers
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.SeedNorms
public import TernaryPeriodPolynomials.Polynomial.Homogeneous

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryPolynomialFiberSystem
open OrdinaryCovectors OrdinaryPolynomialNorm OrdinaryFiberPermutations OrdinarySignedFibers

/-- Literal ordinary polynomial fiber equations, before any group-homology comparison. -/
structure System (F : Covector → TernaryPolynomial) : Prop where
  signed : ∀ s π r,F (permuteRow π (signRow s r))=
    (-1 : ℚ)^s.card • permutePoly π (signPoly s (F r))
  norm : ∀ r,r≠0 → fiberNorm F r=0

/-- Actual seed data give the complete signed-permutation and norm system. -/
theorem seed_system {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (hc : C f=f) (hs : S f=f) (hf : N f=0) (hQ : N Q=0) :
    System (OrdinarySeedFibers.seedValue f P Q) :=
  ⟨seedValue_signed_permutation h hc hs,OrdinarySeedNorms.seedValue_all_norms h hf hQ⟩

private theorem component_permute (n : ℕ) (π : Equiv.Perm (Fin 3)) (f : TernaryPolynomial) :
    MvPolynomial.homogeneousComponent n (permutePoly π f)=permutePoly π (MvPolynomial.homogeneousComponent n f) :=
  homogeneousComponent_bind₁_linear _ (fun i => isHomogeneous_X ℚ (π.symm i)) n f

private theorem component_sign (n : ℕ) (s : Finset (Fin 3)) (f : TernaryPolynomial) :
    MvPolynomial.homogeneousComponent n (signPoly s f)=signPoly s (MvPolynomial.homogeneousComponent n f) := by
  apply homogeneousComponent_bind₁_linear
  intro i
  by_cases hi : i∈s
  · simpa only [ite_eq_left hi] using (isHomogeneous_X ℚ i).neg
  · simpa only [ite_eq_right hi] using isHomogeneous_X ℚ i

private theorem component_A (n : ℕ) (f : TernaryPolynomial) :
    MvPolynomial.homogeneousComponent n (A f)=A (MvPolynomial.homogeneousComponent n f) := by
  apply homogeneousComponent_bind₁_linear
  intro i
  fin_cases i
  · exact (isHomogeneous_X ℚ (1 : Fin 3)).neg
  · exact (isHomogeneous_X ℚ (0 : Fin 3)).sub (isHomogeneous_X ℚ (1 : Fin 3))
  · exact isHomogeneous_X ℚ (2 : Fin 3)

private theorem component_A2 (n : ℕ) (f : TernaryPolynomial) :
    MvPolynomial.homogeneousComponent n (A2 f)=A2 (MvPolynomial.homogeneousComponent n f) := by
  apply homogeneousComponent_bind₁_linear
  intro i
  fin_cases i
  · exact (isHomogeneous_X ℚ (1 : Fin 3)).sub (isHomogeneous_X ℚ (0 : Fin 3))
  · exact (isHomogeneous_X ℚ (0 : Fin 3)).neg
  · exact isHomogeneous_X ℚ (2 : Fin 3)

/-- Homogeneous projection preserves the entire literal fiber system. -/
theorem System.homogeneousComponent {F : Covector → TernaryPolynomial}
    (h : System F) (n : ℕ) : System (fun r => MvPolynomial.homogeneousComponent n (F r)) := by
  constructor
  · intro s π r
    have he := congrArg (MvPolynomial.homogeneousComponent n) (h.signed s π r)
    simpa only [map_smul,component_permute,component_sign] using he
  · intro r hr
    have he := congrArg (MvPolynomial.homogeneousComponent n) (h.norm r hr)
    simpa only [fiberNorm,map_add,map_zero,component_A,component_A2] using he

/-- A homogeneous distinguished seed extends to a homogeneous full fiber system. -/
theorem homogeneous_seed_extension {f P Q : TernaryPolynomial} {n : ℕ}
    (h : SymmetricSeedData f P Q) (hc : C f=f) (hs : S f=f)
    (hf : N f=0) (hQ : N Q=0) (hn : f.IsHomogeneous n) :
    ∃ F : Covector → TernaryPolynomial,
      System F ∧ F ![1,1,1]=f ∧ ∀ r,(F r).IsHomogeneous n := by
  refine ⟨fun r => MvPolynomial.homogeneousComponent n (OrdinarySeedFibers.seedValue f P Q r),
    (seed_system h hc hs hf hQ).homogeneousComponent n,?_,?_⟩
  · change MvPolynomial.homogeneousComponent n (OrdinarySeedFibers.seedValue f P Q ![1,1,1])=f
    rw [OrdinarySeedFibers.seedValue_three]
    simp [homogeneousComponent_of_mem hn]
  · intro r
    exact homogeneousComponent_isHomogeneous n _

end TernaryPoly.OrdinaryPolynomialFiberSystem
