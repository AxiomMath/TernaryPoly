module

public import TernaryPeriodPolynomials.Topology.Rational.Compact.NeighborhoodAlgebra
public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionMaps

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalCompactNeighborhood
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology RationalRelativeSingular

variable {X : Type} [TopologicalSpace X]

/-- Actual relative chains supported on a set are chains modulo its complement. -/
abbrev supportChains (K : Set X) := relativeChains Kᶜ

/-- The literal quotient projection to chains supported on a set. -/
abbrev supportProjection (K : Set X) : chains X ⟶ supportChains K :=
  cokernel.π (inclusion Kᶜ)

/-- Actual support restriction is the identity map of relative pairs. -/
def restriction (K L : Set X) (h : L ⊆ K) : supportChains K ⟶ supportChains L :=
  relativeMap (ContinuousMap.id X) Kᶜ Lᶜ (fun _ hz hl => hz (h hl))

/-- The actual support restriction commutes with the quotient projections. -/
theorem restriction_projection (K L : Set X) (h : L ⊆ K) :
    supportProjection K ≫ restriction K L h = supportProjection L := by
  simp [restriction, supportProjection, relativeMap, cokernel.map,
    RationalSingularAugmentation.chainMap]

/-- Degreewise, restriction retains the original absolute chain. -/
theorem restriction_projection_apply (K L : Set X) (h : L ⊆ K) (n : ℕ)
    (a : (chains X).X n) :
    (restriction K L h).f n ((supportProjection K).f n a) =
      (supportProjection L).f n a :=
  congrArg (fun f => f a) (HomologicalComplex.congr_hom (restriction_projection K L h) n)

/-- The literal quotient projection commutes with differentials on elements. -/
theorem projection_d (K : Set X) (i j : ℕ) (a : (chains X).X i) :
    (supportChains K).d i j ((supportProjection K).f i a) =
      (supportProjection K).f j ((chains X).d i j a) :=
  congrArg (fun f => f a) ((supportProjection K).comm i j)

/-- A quotient chain is a cycle exactly when its boundary lifts from complement chains. -/
theorem projected_cycle_iff (K : Set X) (n : ℕ) (a : (chains X).X n) :
    (supportChains K).d n (n-1) ((supportProjection K).f n a) = 0 ↔
      ∃ b : (chains (Kᶜ : Set X)).X (n-1),
        (inclusion Kᶜ).f (n-1) b = (chains X).d n (n-1) a := by
  rw [projection_d]
  exact SingularLocalCap.RelativeAlgebra.projection_zero_iff (inclusion Kᶜ) (n-1) _

/-- Every actual supported homology class is represented by an absolute chain. -/
theorem exists_projected_cycleClass (K : Set X) (n : ℕ) (c : (supportChains K).homology n) :
    ∃ (a : (chains X).X n)
      (ha : (supportChains K).d n (n-1) ((supportProjection K).f n a) = 0),
      cycleClass (supportChains K) n ((supportProjection K).f n a) ha = c := by
  obtain ⟨q, hq, rfl⟩ := exists_cycleClass (supportChains K) n c
  obtain ⟨a, rfl⟩ := SingularLocalCap.RelativeAlgebra.projection_surjective (inclusion Kᶜ) n q
  exact ⟨a, hq, rfl⟩

/-- A represented relative class is zero exactly when an absolute bounding chain exists,
up to a chain of the complement. -/
theorem projected_cycleClass_eq_zero_iff (K : Set X) (n : ℕ) (a : (chains X).X n)
    (ha : (supportChains K).d n (n-1) ((supportProjection K).f n a) = 0) :
    cycleClass (supportChains K) n ((supportProjection K).f n a) ha = 0 ↔
      ∃ b : (chains X).X (n+1), ∃ e : (chains (Kᶜ : Set X)).X n,
        (inclusion Kᶜ).f n e = a - (chains X).d (n+1) n b := by
  rw [cycleClass_eq_zero_iff]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨b, rfl⟩ := SingularLocalCap.RelativeAlgebra.projection_surjective (inclusion Kᶜ) (n+1) q
    refine ⟨b, (SingularLocalCap.RelativeAlgebra.projection_zero_iff (inclusion Kᶜ) n _).mp ?_⟩
    rw [map_sub, ← projection_d, hq, sub_self]
  · rintro ⟨b, e, he⟩
    refine ⟨(supportProjection K).f (n+1) b, ?_⟩
    have hz := (SingularLocalCap.RelativeAlgebra.projection_zero_iff (inclusion Kᶜ) n _).mpr ⟨e, he⟩
    rw [map_sub, ← projection_d, sub_eq_zero] at hz
    exact hz.symm

/-- A literal support restriction carries projected cycles to projected cycles. -/
theorem restricted_cycle (K L : Set X) (h : L ⊆ K) (n : ℕ) (a : (chains X).X n)
    (ha : (supportChains K).d n (n-1) ((supportProjection K).f n a) = 0) :
    (supportChains L).d n (n-1) ((supportProjection L).f n a) = 0 := by
  rw [← restriction_projection_apply K L h n a]
  have hc := congrArg (fun f => f ((supportProjection K).f n a))
    ((restriction K L h).comm n (n-1))
  change (supportChains L).d n (n-1)
    ((restriction K L h).f n ((supportProjection K).f n a)) =
      (restriction K L h).f (n-1)
        ((supportChains K).d n (n-1) ((supportProjection K).f n a)) at hc
  rw [hc, ha, map_zero]

/-- Restriction preserves represented classes using the same absolute chain. -/
theorem restriction_cycleClass (K L : Set X) (h : L ⊆ K) (n : ℕ) (a : (chains X).X n)
    (ha : (supportChains K).d n (n-1) ((supportProjection K).f n a) = 0)
    (hb : (supportChains L).d n (n-1) ((supportProjection L).f n a) = 0) :
    homologyMap (restriction K L h) n
        (cycleClass (supportChains K) n ((supportProjection K).f n a) ha) =
      cycleClass (supportChains L) n ((supportProjection L).f n a) hb := by
  have hf : (supportChains L).d n (n-1)
      ((restriction K L h).f n ((supportProjection K).f n a)) = 0 := by
    rw [restriction_projection_apply]
    exact hb
  rw [cycleClass_naturality _ _ _ _ _ hf]
  congr 1
  exact restriction_projection_apply K L h n a

end TernaryPoly.RationalCompactNeighborhood
