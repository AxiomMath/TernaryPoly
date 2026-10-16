module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceData
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.BadLineFinite

@[expose] public section


/-!
# The level-three sign-twisted Levi cocycle data

The analogue of `LineLeviCocycleData` for a vector that is only fixed by the bad-line Levi level
(the level-three level), not by all of `GL₂(Ẑ)`: the field `spherical` is replaced by
`levelFixed`, the membership of all lift values in `badLevelSubspace σ`.  Every spherical datum is a
level-three datum (`LineLeviCocycleData.toLevel3`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The sign-twisted analytic Levi cocycle of a cuspidal representation, with values whose lifts are
fixed by the bad-line (level-three) Levi level only. -/
structure LineLeviCocycleData3 (σ : CuspidalRepresentation) (n : ℕ) where
  α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)
  cocycle : ∀ g h x,
    α (g * h) x = α g x + lineSgn g • binaryCohomologicalAction n g (α h) x
  orth : ∀ k : BinaryRealGL, k.val.transpose * k.val = 1 → ∀ x, α k x = 0
  lift : (Fin 2 →₀ ℕ) → BinaryRealGL → σ.smooth
  lift_realize : ∀ μ g A, σ.realize (lift μ g) A = (α g A).val.coeff μ
  lift_smooth : ∀ μ, Smooth (fun x : Fin 1 → BinaryRealGL => (lift μ (x 0)).val)
  scalar_smooth : ∀ μ A, Smooth (fun x : Fin 1 → BinaryRealGL => (α (x 0) A).val.coeff μ)
  levelFixed : ∀ μ g, (lift μ g).val ∈ badLevelSubspace σ

theorem sphericalSubspace_le_badLevelSubspace (σ : CuspidalRepresentation) :
    sphericalSubspace σ ≤ badLevelSubspace σ :=
  fun _ hv k _ => hv k

/-- A spherical datum is a level-three datum. -/
def LineLeviCocycleData.toLevel3 {σ : CuspidalRepresentation} {n : ℕ}
    (E : LineLeviCocycleData σ n) : LineLeviCocycleData3 σ n where
  α := E.α
  cocycle := E.cocycle
  orth := E.orth
  lift := E.lift
  lift_realize := E.lift_realize
  lift_smooth := E.lift_smooth
  scalar_smooth := E.scalar_smooth
  levelFixed := fun μ g => sphericalSubspace_le_badLevelSubspace σ (E.spherical μ g)

end TernaryPeriodPolynomials.SourceConstruction

end
