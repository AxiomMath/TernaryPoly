module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Support

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set SmoothLocalDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {U : Set OrbitSpace} {n : ℕ}

/-- Compact support on the quotient open set: projected closed support is compact and lies
inside that open set. This includes the boundary condition required for genuine compact support. -/
def HasQuotientCompactSupport (w : EquivariantForm ρ U n) : Prop :=
  IsCompact (quotientSupport w) ∧ quotientSupport w ⊆ U

def compactSupportSubmodule (U : Set OrbitSpace) (n : ℕ) : Submodule ℝ (EquivariantForm ρ U n) where
  carrier := {w | HasQuotientCompactSupport ρ w}
  zero_mem' := by simp [HasQuotientCompactSupport]
  add_mem' := by
    intro w z hw hz
    exact ⟨(hw.1.union hz.1).of_isClosed_subset isClosed_closure (quotientSupport_add w z),
      (quotientSupport_add w z).trans (union_subset hw.2 hz.2)⟩
  smul_mem' := by
    intro c w hw
    exact ⟨hw.1.of_isClosed_subset isClosed_closure (quotientSupport_smul c w),
      (quotientSupport_smul c w).trans hw.2⟩

abbrev CompactSupportForm (U : Set OrbitSpace) (n : ℕ) := compactSupportSubmodule ρ U n

instance compactSupportFormAddCommGroup (U : Set OrbitSpace) (n : ℕ) :
    AddCommGroup (CompactSupportForm ρ U n) :=
  Submodule.addCommGroup (R := ℝ) (M := EquivariantForm ρ U n)
    (module_M := inferInstance) (compactSupportSubmodule ρ U n)

theorem hasQuotientCompactSupport_differential (hU : IsOpen U) (w : EquivariantForm ρ U n)
    (hw : HasQuotientCompactSupport ρ w) : HasQuotientCompactSupport ρ (differential ρ hU n w) :=
  ⟨hw.1.of_isClosed_subset isClosed_closure (quotientSupport_differential hU w),
    (quotientSupport_differential hU w).trans hw.2⟩

/-- The literal exterior derivative on genuinely quotient-compactly-supported forms. -/
def compactDifferential (hU : IsOpen U) (n : ℕ) :
    CompactSupportForm ρ U n →ₗ[ℝ] CompactSupportForm ρ U (n + 1) where
  toFun w := ⟨differential ρ hU n w.val, hasQuotientCompactSupport_differential ρ hU w.val w.property⟩
  map_add' w z := Subtype.ext (map_add _ w.val z.val)
  map_smul' c w := Subtype.ext (map_smul _ c w.val)

@[simp] theorem compactDifferential_coe (hU : IsOpen U) (w : CompactSupportForm ρ U n) :
    (compactDifferential ρ hU n w).val = differential ρ hU n w.val := rfl

theorem compactDifferential_squared (hU : IsOpen U) (n : ℕ) (w : CompactSupportForm ρ U n) :
    compactDifferential ρ hU (n + 1) (compactDifferential ρ hU n w) = 0 :=
  Subtype.ext (differential_squared ρ hU n w.val)

/-- The actual compact-support local-coefficient de Rham complex on the quotient. -/
def compactCoveringComplex (hU : IsOpen U) : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℝ (CompactSupportForm ρ U n))
    (fun n => ModuleCat.ofHom (compactDifferential ρ hU n)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      exact compactDifferential_squared ρ hU n w)

abbrev globalCompactComplex : CochainComplex (ModuleCat ℝ) ℕ := compactCoveringComplex ρ isOpen_univ

end TernaryPoly.SmoothCoveringDeRham
