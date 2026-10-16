module

public import TernaryPeriodPolynomials.Topology.Rational.Sphere.Band
public import TernaryPeriodPolynomials.Topology.Singular.SubdivisionMayerVietoris

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalSphere
open CategoryTheory Limits TopologicalSpace ContractibleSingularHomology

/-- The actual upper punctured sphere as an open set. -/
def upperOpens (n : ℕ) : Opens (Sphere (n+1)) :=
  ⟨upperPunctured n, isOpen_upperPunctured n⟩

/-- The actual lower punctured sphere as an open set. -/
def lowerOpens (n : ℕ) : Opens (Sphere (n+1)) :=
  ⟨lowerPunctured n, isOpen_lowerPunctured n⟩

instance (n : ℕ) : ContractibleSpace (upperOpens n) := contractible_upperPunctured n
instance (n : ℕ) : ContractibleSpace (lowerOpens n) := contractible_lowerPunctured n

theorem upperOpens_sup_lowerOpens (n : ℕ) : upperOpens n ⊔ lowerOpens n = ⊤ :=
  Opens.ext (upper_union_lower n)

/-- Actual rational homology of the doubly punctured sphere identifies with that of the
lower-dimensional sphere using normalized equatorial projection. -/
def bandHomologyIso (n k : ℕ) :
    (chains (sphereBand n)).homology k ≅ (chains (Sphere n)).homology k :=
  (chainHomotopyEquiv (sphereBandHomotopyEquiv n)).toHomologyIso k

/-- The actual rational Mayer–Vietoris connecting isomorphism yields the sphere recurrence
in every positive lower degree. The degree-zero case is deliberately excluded. -/
def suspensionIso (n k : ℕ) (hk : k ≠ 0) :
    (chains (Sphere (n+1))).homology (k+1) ≅ (chains (Sphere n)).homology k :=
  SingularSubdivision.mayerVietorisContractibleIso (Sphere (n+1))
    (upperOpens n) (lowerOpens n) (upperOpens_sup_lowerOpens n) k hk ≪≫
    bandHomologyIso n k

/-- The recurrence transports actual zero-homology statements. -/
theorem homology_succ_isZero_iff (n k : ℕ) (hk : k ≠ 0) :
    IsZero ((chains (Sphere (n+1))).homology (k+1)) ↔
      IsZero ((chains (Sphere n)).homology k) :=
  ⟨fun h => h.of_iso (suspensionIso n k hk).symm,
    fun h => h.of_iso (suspensionIso n k hk)⟩

end TernaryPoly.RationalSphere
