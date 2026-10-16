module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Equivariant

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set SmoothLocalDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The literal exterior differential on actual equivariant covering forms. -/
def differential (ρ : Representation ℝ DeckGroup F) {U : Set OrbitSpace} (hU : IsOpen U) (n : ℕ) :
    EquivariantForm ρ U n →ₗ[ℝ] EquivariantForm ρ U (n + 1) where
  toFun w := ⟨d (liftedDomain_isOpen hU) n w.val, equivariant_d ρ hU w.val w.property⟩
  map_add' w z := by
    apply Subtype.ext
    exact map_add (d (liftedDomain_isOpen hU) n) w.val z.val
  map_smul' c w := by
    apply Subtype.ext
    exact map_smul (d (liftedDomain_isOpen hU) n) c w.val

@[simp] theorem differential_coe (ρ : Representation ℝ DeckGroup F) {U : Set OrbitSpace}
    (hU : IsOpen U) (n : ℕ) (w : EquivariantForm ρ U n) :
    (differential ρ hU n w).val = d (liftedDomain_isOpen hU) n w.val := rfl

theorem differential_squared (ρ : Representation ℝ DeckGroup F) {U : Set OrbitSpace}
    (hU : IsOpen U) (n : ℕ) (w : EquivariantForm ρ U n) :
    differential ρ hU (n + 1) (differential ρ hU n w) = 0 := by
  apply Subtype.ext
  exact d_squared (liftedDomain_isOpen hU) n w.val

/-- The actual local-coefficient de Rham complex over each open subset of the quotient. -/
def coveringComplex (ρ : Representation ℝ DeckGroup F) {U : Set OrbitSpace} (hU : IsOpen U) :
    CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℝ (EquivariantForm ρ U n))
    (fun n => ModuleCat.ofHom (differential ρ hU n)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      exact differential_squared ρ hU n w)

/-- Global forms are equivariant forms over the actual full covering. -/
abbrev globalComplex (ρ : Representation ℝ DeckGroup F) : CochainComplex (ModuleCat ℝ) ℕ :=
  coveringComplex ρ isOpen_univ

end TernaryPoly.SmoothCoveringDeRham
