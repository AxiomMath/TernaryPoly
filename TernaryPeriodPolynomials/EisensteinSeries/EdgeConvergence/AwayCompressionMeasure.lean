module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Coordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.ThreeMeasure
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.SphericalLevel

@[expose] public section


/-!
# The spherical `GL₂` preserves the finite radical measure away from three

A finite adelic `GL₂` matrix acts on the coordinates `(u₁, u₂)` of the radical away from `∞` and `3`
as a row vector. When both the matrix and its inverse are integral, the action is a continuous
additive automorphism of `FiniteAwayThree²` preserving the integral lattice, hence the normalized
Haar measure.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory TopologicalSpace
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.RepresentationTheory

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

theorem finiteThree_away (value : FiniteAwayThree) : finiteThree value.val = 0 := value.property

theorem rowAction_three (m : BinaryFiniteGL) (u : FiniteAwayThree × FiniteAwayThree) (j : Fin 2) :
    finiteThree (u.1.val * m.val 0 j + u.2.val * m.val 1 j) = 0 := by
  rw [map_add, map_mul, map_mul, finiteThree_away u.1, finiteThree_away u.2, zero_mul, zero_mul,
    add_zero]

/-- The row-vector action of a finite adelic `GL₂` matrix on the radical coordinates away from
`∞` and `3`. -/
def awayRowAction (m : BinaryFiniteGL) (u : FiniteAwayThree × FiniteAwayThree) :
    FiniteAwayThree × FiniteAwayThree :=
  (⟨u.1.val * m.val 0 0 + u.2.val * m.val 1 0, rowAction_three m u 0⟩,
   ⟨u.1.val * m.val 0 1 + u.2.val * m.val 1 1, rowAction_three m u 1⟩)

@[simp] theorem awayRowAction_fst_val (m : BinaryFiniteGL) (u : FiniteAwayThree × FiniteAwayThree) :
    ((awayRowAction m u).1 : FiniteAdeles) = u.1.val * m.val 0 0 + u.2.val * m.val 1 0 := rfl

@[simp] theorem awayRowAction_snd_val (m : BinaryFiniteGL) (u : FiniteAwayThree × FiniteAwayThree) :
    ((awayRowAction m u).2 : FiniteAdeles) = u.1.val * m.val 0 1 + u.2.val * m.val 1 1 := rfl

theorem awayRowAction_mul (m n : BinaryFiniteGL) (u : FiniteAwayThree × FiniteAwayThree) :
    awayRowAction n (awayRowAction m u) = awayRowAction (m * n) u := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp only [awayRowAction_fst_val, awayRowAction_snd_val, Units.val_mul, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem awayRowAction_one (u : FiniteAwayThree × FiniteAwayThree) : awayRowAction 1 u = u := by
  apply Prod.ext <;> apply Subtype.ext <;> simp

theorem awayRowAction_add (m : BinaryFiniteGL) (u v : FiniteAwayThree × FiniteAwayThree) :
    awayRowAction m (u + v) = awayRowAction m u + awayRowAction m v := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp only [awayRowAction_fst_val, awayRowAction_snd_val, Prod.fst_add, Prod.snd_add,
      AddSubgroup.coe_add] <;> ring

theorem awayRowAction_continuous (m : BinaryFiniteGL) : Continuous (awayRowAction m) := by
  unfold awayRowAction
  exact Continuous.prodMk (Continuous.subtype_mk (by fun_prop) _)
    (Continuous.subtype_mk (by fun_prop) _)

/-- The row-vector action of an invertible matrix as a continuous additive automorphism. -/
def awayRowEquiv (m : BinaryFiniteGL) :
    (FiniteAwayThree × FiniteAwayThree) ≃ₜ+ (FiniteAwayThree × FiniteAwayThree) where
  toFun := awayRowAction m
  invFun := awayRowAction m⁻¹
  left_inv u := by rw [awayRowAction_mul, mul_inv_cancel, awayRowAction_one]
  right_inv u := by rw [awayRowAction_mul, inv_mul_cancel, awayRowAction_one]
  map_add' := awayRowAction_add m
  continuous_toFun := awayRowAction_continuous m
  continuous_invFun := awayRowAction_continuous m⁻¹

/-- The integral lattice of `FiniteAwayThree`. -/
abbrev awayLattice : Set FiniteAwayThree := Subtype.val ⁻¹' Set.range integralEmbedding

theorem awayRowAction_lattice {m : BinaryFiniteGL} (hm : m ∈ sphericalFinite)
    {u : FiniteAwayThree × FiniteAwayThree} (hu : u ∈ awayLattice ×ˢ awayLattice) :
    awayRowAction m u ∈ awayLattice ×ˢ awayLattice := by
  obtain ⟨m₀, rfl⟩ := hm
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hu
  constructor
  · refine ⟨x * m₀.val 0 0 + y * m₀.val 1 0, ?_⟩
    rw [awayRowAction_fst_val, map_add, map_mul, map_mul, hx, hy]
    simp [GeneralLinearGroup.map_apply]
  · refine ⟨x * m₀.val 0 1 + y * m₀.val 1 1, ?_⟩
    rw [awayRowAction_snd_val, map_add, map_mul, map_mul, hx, hy]
    simp [GeneralLinearGroup.map_apply]

theorem awayRowAction_preimage_lattice {m : BinaryFiniteGL} (hm : m ∈ sphericalFinite) :
    awayRowAction m ⁻¹' (awayLattice ×ˢ awayLattice) = awayLattice ×ˢ awayLattice := by
  ext u
  constructor
  · intro hu
    have back := awayRowAction_lattice (sphericalFinite.inv_mem hm) hu
    rwa [awayRowAction_mul, mul_inv_cancel, awayRowAction_one] at back
  · exact awayRowAction_lattice hm

/-- The normalized product measure on the finite radical coordinates. -/
abbrev awayProductMeasure : Measure (FiniteAwayThree × FiniteAwayThree) :=
  finiteAwayThreeMeasure.prod finiteAwayThreeMeasure

/-- **The spherical `GL₂` preserves the finite radical measure.** -/
theorem awayRowAction_measurePreserving {m : BinaryFiniteGL} (hm : m ∈ sphericalFinite) :
    MeasurePreserving (awayRowAction m) awayProductMeasure awayProductMeasure := by
  let K₀ : PositiveCompacts (FiniteAwayThree × FiniteAwayThree) :=
    finiteAwayThreeUnitCompact ×ˢ finiteAwayThreeUnitCompact
  have hK : (K₀ : Set (FiniteAwayThree × FiniteAwayThree)) = awayLattice ×ˢ awayLattice := rfl
  have measurable : Measurable (awayRowAction m) := (awayRowAction_continuous m).measurable
  refine ⟨measurable, ?_⟩
  have haar : (awayProductMeasure.map (awayRowEquiv m)).IsAddHaarMeasure :=
    ContinuousAddEquiv.isAddHaarMeasure_map awayProductMeasure (awayRowEquiv m)
  have mapEquality : awayProductMeasure.map (awayRowAction m) =
      awayProductMeasure.map (awayRowEquiv m) := rfl
  have hval : (awayProductMeasure.map (awayRowEquiv m)) K₀ = awayProductMeasure K₀ := by
    rw [← mapEquality, Measure.map_apply measurable K₀.isCompact.measurableSet, hK,
      awayRowAction_preimage_lattice hm]
  have h1 := Measure.addHaarMeasure_unique (awayProductMeasure.map (awayRowEquiv m)) K₀
  have h2 := Measure.addHaarMeasure_unique awayProductMeasure K₀
  rw [mapEquality, h1, hval]
  exact h2.symm

theorem awayRadicalMeasure_eq : awayRadicalMeasure = awayProductMeasure := rfl

/-- Invariance of integrals under the spherical row action. -/
theorem integral_awayRowAction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : BinaryFiniteGL} (hm : m ∈ sphericalFinite) (φ : FiniteAwayThree × FiniteAwayThree → E) :
    (∫ u, φ (awayRowAction m u) ∂awayRadicalMeasure) = ∫ u, φ u ∂awayRadicalMeasure :=
  (awayRowAction_measurePreserving hm).integral_comp
    (awayRowEquiv m).toHomeomorph.measurableEmbedding φ

end TernaryPeriodPolynomials.EdgeConvergence
