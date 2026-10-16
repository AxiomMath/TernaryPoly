module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.BoundaryClasses
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.RelativeAlgebra
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalCompactNeighborhood
open CategoryTheory Limits HomologicalComplex
open SingularLocalCap.BoundaryClasses

variable (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)

/-- An actual chain cycle determines an element of the actual homology object. -/
def cycleClass (a : K.X n) (ha : K.d n (n-1) a = 0) : K.homology n :=
  classMap K n (elementMap a) (by
    rw [elementMap_comp, ha]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp [elementMap]) 1

/-- The image of a represented homology class in opcycles is the chain projection. -/
theorem cycleClass_opcycles (a : K.X n) (ha : K.d n (n-1) a = 0) :
    K.homologyι n (cycleClass K n a ha) = K.pOpcycles n a := by
  unfold cycleClass classMap
  change ((K.liftCycles _ _ _ _ ≫ K.homologyπ n) ≫ K.homologyι n) 1 = _
  rw [Category.assoc, homology_π_ι, ← Category.assoc, liftCycles_i]
  simp [elementMap]

/-- Every actual homology class has an actual chain-cycle representative. -/
theorem exists_cycleClass (c : K.homology n) :
    ∃ (a : K.X n) (ha : K.d n (n-1) a = 0), cycleClass K n a ha = c := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance c
  have hz : K.d n (n-1) (K.iCycles n z) = 0 := by
    exact congrArg (fun f => f z) (K.iCycles_d n (n-1))
  refine ⟨K.iCycles n z, hz, ?_⟩
  apply (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  rw [cycleClass_opcycles]
  exact (congrArg (fun f => f z) (K.homology_π_ι n)).symm

/-- A represented cycle is zero precisely when it is an actual boundary. -/
theorem cycleClass_eq_zero_iff (a : K.X n) (ha : K.d n (n-1) a = 0) :
    cycleClass K n a ha = 0 ↔ ∃ b : K.X (n+1), K.d (n+1) n b = a := by
  have hi := (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  have hzero : cycleClass K n a ha = 0 ↔ K.pOpcycles n a = 0 := by
    constructor
    · intro h
      rw [← cycleClass_opcycles K n a ha, h, map_zero]
    · intro h
      apply hi
      rw [cycleClass_opcycles, map_zero, h]
  rw [hzero]
  change (K.sc n).pOpcycles a = 0 ↔ _
  erw [(K.sc n).moduleCat_pOpcycles_eq_zero_iff]
  change (∃ b : K.X ((ComplexShape.down ℕ).prev n),
    K.d ((ComplexShape.down ℕ).prev n) n b = a) ↔ _
  rw [ChainComplex.prev]

/-- A chain map sends a represented cycle to the class of its literal image chain. -/
theorem cycleClass_naturality {L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L)
    (a : K.X n) (ha : K.d n (n-1) a = 0)
    (hfa : L.d n (n-1) (f.f n a) = 0) :
    homologyMap f n (cycleClass K n a ha) = cycleClass L n (f.f n a) hfa := by
  apply (ModuleCat.mono_iff_injective (L.homologyι n)).mp inferInstance
  rw [cycleClass_opcycles]
  change (homologyMap f n ≫ L.homologyι n) _ = _
  rw [homologyι_naturality]
  change opcyclesMap f n (K.homologyι n _) = _
  rw [cycleClass_opcycles]
  exact congrArg (fun g => g a) (p_opcyclesMap f n)

end TernaryPoly.RationalCompactNeighborhood
