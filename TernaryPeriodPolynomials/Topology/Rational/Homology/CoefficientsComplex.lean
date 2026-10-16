module

public import TernaryPeriodPolynomials.Topology.Rational.Homology.CoefficientsNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalHomologyCoefficients
open CategoryTheory HomologicalComplex
open SingularLocalCap SingularLocalCap.Homology
variable (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (V : ModuleCat.{0} ℚ)

/-- The actual V-valued Hom cochain complex of an arbitrary rational chain complex. -/
abbrev homCochains : CochainComplex (ModuleCat.{0} ℚ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℚ (K.X n →ₗ[ℚ] V))
    (fun n => ModuleCat.ofHom (precompose (K.d (n+1) n) V)) (fun n => by
      apply ModuleCat.hom_ext
      ext φ c
      have h := congrArg (fun f => f c) (K.d_comp_d (n+2) (n+1) n)
      change K.d (n+1) n (K.d (n+2) (n+1) c) = 0 at h
      change φ (K.d (n+1) n (K.d (n+2) (n+1) c)) = 0
      rw [h,map_zero])

/-- In every pair of degrees, including the bottom-degree zero differential, the Hom
differential is exactly precomposition with the reversed actual chain differential. -/
theorem homCochains_d (i j : ℕ) :
    (homCochains K V).d i j = ModuleCat.ofHom (precompose (K.d j i) V) := by
  by_cases h : i+1 = j
  · subst j
    simp only [homCochains, CochainComplex.of_d]
  · rw [(homCochains K V).shape i j h, K.shape j i h]
    apply ModuleCat.hom_ext
    ext φ c
    exact (map_zero φ).symm

/-- The three-degree part of the actual Hom cochain complex is the actual Hom dual
of the reversed three-degree part of the chain complex. -/
def shortDualIso (a : ℕ) :
    (homCochains K V).sc' (a-1) a (a+1) ≅ dual (K.sc' (a+1) a (a-1)) V :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      exact (homCochains_d K V (a-1) a).symm)
    (by
      exact (homCochains_d K V a (a+1)).symm)

/-- The genuine V-valued rational universal-coefficient isomorphism for an actual chain complex. -/
def homologyEvaluationEquiv (a : ℕ) :
    (homCochains K V).homology a ≃ₗ[ℚ] (K.homology a →ₗ[ℚ] V) :=
  ((homCochains K V).homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).toLinearEquiv ≪≫ₗ
    ((ShortComplex.homologyFunctor (ModuleCat ℚ)).mapIso (shortDualIso K V a)).toLinearEquiv ≪≫ₗ
    evaluationEquiv (K.sc' (a+1) a (a-1)) V ≪≫ₗ
    LinearEquiv.arrowCongr
      (K.homologyIsoSc' (a+1) a (a-1) (down_prev _) (down_next _)).symm.toLinearEquiv
      (LinearEquiv.refl ℚ V)

end TernaryPoly.RationalHomologyCoefficients
