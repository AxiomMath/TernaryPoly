module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PrimeMeasure
public import Mathlib.Topology.Algebra.Group.Matrix

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.TopologicalMatrices

theorem units_map_range {R S : Type*} [Monoid R] [Monoid S]
    (hom : R →* S) (injective : Function.Injective hom) :
    Set.range (Units.map hom) =
      {unit : Sˣ | unit.val ∈ Set.range hom ∧ unit.inv ∈ Set.range hom} := by
  ext unit
  constructor
  · rintro ⟨source, rfl⟩
    exact ⟨⟨source.val, rfl⟩, ⟨source.inv, rfl⟩⟩
  · rintro ⟨⟨value, valueEquality⟩, ⟨inverse, inverseEquality⟩⟩
    have left : value * inverse = 1 := by
      apply injective
      rw [map_mul, valueEquality, inverseEquality, unit.val_inv, map_one]
    have right : inverse * value = 1 := by
      apply injective
      rw [map_mul, valueEquality, inverseEquality, unit.inv_val, map_one]
    refine ⟨⟨value, inverse, left, right⟩, ?_⟩
    exact Units.ext valueEquality

theorem units_map_isOpenEmbedding {R S : Type*} [Monoid R] [Monoid S]
    [TopologicalSpace R] [TopologicalSpace S] (hom : R →* S)
    (embedding : Topology.IsOpenEmbedding hom) :
    Topology.IsOpenEmbedding (Units.map hom) := by
  refine ⟨embedding.isEmbedding.units_map, ?_⟩
  rw [units_map_range hom embedding.injective]
  exact (embedding.isOpen_range.preimage Units.continuous_val).inter
    (embedding.isOpen_range.preimage Units.continuous_coe_inv)

theorem matrixMap_isOpenEmbedding {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] {size : ℕ} (hom : R →+* S)
    (embedding : Topology.IsOpenEmbedding hom) :
    Topology.IsOpenEmbedding (fun matrix : Matrix (Fin size) (Fin size) R => matrix.map hom) := by
  exact Topology.IsOpenEmbedding.piMap (fun _ : Fin size =>
    Topology.IsOpenEmbedding.piMap (fun _ : Fin size => embedding))

theorem generalLinearMap_isOpenEmbedding {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] {size : ℕ} (hom : R →+* S)
    (embedding : Topology.IsOpenEmbedding hom) :
    Topology.IsOpenEmbedding (GeneralLinearGroup.map (n := Fin size) hom) := by
  apply units_map_isOpenEmbedding
  exact matrixMap_isOpenEmbedding hom embedding

theorem generalLinearMap_continuous {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] {size : ℕ} (hom : R →+* S)
    (continuous : Continuous hom) :
    Continuous (GeneralLinearGroup.map (n := Fin size) hom) := by
  apply Units.continuous_map
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  exact continuous.comp ((continuous_apply column).comp (continuous_apply row))

theorem integralGL_isOpenEmbedding :
    Topology.IsOpenEmbedding (GeneralLinearGroup.map (n := Fin 3) integralEmbedding) :=
  generalLinearMap_isOpenEmbedding integralEmbedding integralEmbedding_isOpenEmbedding

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.TopologicalMatrices
