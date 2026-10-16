module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V W U : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

def surjectiveLinearDescent (projection : V →ₗ[ℂ] W) (surjective : Function.Surjective projection)
    (coordinate : V →ₗ[ℂ] U)
    (fibers : ∀ first second, projection first = projection second → coordinate first = coordinate second) :
    W →ₗ[ℂ] U where
  toFun vector := coordinate (surjective vector).choose
  map_add' first second := by
    calc
      _ = coordinate ((surjective first).choose + (surjective second).choose) :=
        fibers _ _ (by rw [map_add, (surjective first).choose_spec, (surjective second).choose_spec,
          (surjective (first + second)).choose_spec])
      _ = _ := map_add coordinate _ _
  map_smul' scalar vector := by
    calc
      _ = coordinate (scalar • (surjective vector).choose) :=
        fibers _ _ (by rw [map_smul, (surjective vector).choose_spec, (surjective (scalar • vector)).choose_spec])
      _ = _ := map_smul coordinate scalar _

theorem surjectiveLinearDescent_apply (projection : V →ₗ[ℂ] W)
    (surjective : Function.Surjective projection) (coordinate : V →ₗ[ℂ] U)
    (fibers : ∀ first second, projection first = projection second → coordinate first = coordinate second)
    (vector : V) :
    surjectiveLinearDescent projection surjective coordinate fibers (projection vector) = coordinate vector :=
  fibers _ _ (surjective (projection vector)).choose_spec

theorem surjectiveLinearDescent_bijective (projection : V →ₗ[ℂ] W)
    (surjective : Function.Surjective projection) (coordinate : V →ₗ[ℂ] U)
    (coordinate_surjective : Function.Surjective coordinate)
    (fibers : ∀ first second, projection first = projection second ↔ coordinate first = coordinate second) :
    Function.Bijective (surjectiveLinearDescent projection surjective coordinate (fun first second => (fibers first second).mp)) := by
  constructor
  · intro first second equality
    obtain ⟨first, rfl⟩ := surjective first
    obtain ⟨second, rfl⟩ := surjective second
    rw [surjectiveLinearDescent_apply, surjectiveLinearDescent_apply] at equality
    exact (fibers first second).mpr equality
  · intro vector
    obtain ⟨source, rfl⟩ := coordinate_surjective vector
    exact ⟨projection source, surjectiveLinearDescent_apply projection surjective coordinate _ source⟩

def surjectiveLinearCoordinateEquiv (projection : V →ₗ[ℂ] W)
    (surjective : Function.Surjective projection) (coordinate : V →ₗ[ℂ] U)
    (coordinate_surjective : Function.Surjective coordinate)
    (fibers : ∀ first second, projection first = projection second ↔ coordinate first = coordinate second) :
    W ≃ₗ[ℂ] U :=
  LinearEquiv.ofBijective
    (surjectiveLinearDescent projection surjective coordinate (fun first second => (fibers first second).mp))
    (surjectiveLinearDescent_bijective projection surjective coordinate coordinate_surjective fibers)

theorem surjectiveLinearCoordinateEquiv_apply (projection : V →ₗ[ℂ] W)
    (surjective : Function.Surjective projection) (coordinate : V →ₗ[ℂ] U)
    (coordinate_surjective : Function.Surjective coordinate)
    (fibers : ∀ first second, projection first = projection second ↔ coordinate first = coordinate second)
    (vector : V) :
    surjectiveLinearCoordinateEquiv projection surjective coordinate coordinate_surjective fibers
      (projection vector) = coordinate vector :=
  surjectiveLinearDescent_apply projection surjective coordinate (fun first second => (fibers first second).mp) vector

end TernaryPeriodPolynomials.SphericalDetection.Helpers
