module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.FlatLocalizeD
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.PairValueAux
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.DegreeHomotopyR2
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.PointTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.ChartChain

@[expose] public section


/-!
# The glued flat over the chart box and its chart coordinates

For a frame `F`, `VO F` is the part of the glued flat `FD` lying over the chart box, `kap` its map to the chart `UT` of the base, and
`VO_coords` the coordinates of a point of `VO F`: the chamber `k` and the simple-root parameters `(s, t) ∈ (0,1]²`, with the plane
coordinates `ρ ∘ ψ ∘ s` of its chart point equal to `hexM k · (log s, log t)` and the straight fan coordinate `LamD` equal to
`hexM k · (s - 1, t - 1)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularLocalSupport
  TernaryPoly.SingularLocalCoefficient TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap.Descent
  TernaryPoly.EquivariantSingularResolution TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
  TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceBordifiedCohomology
  TernaryPoly.SymmetricSpaceRationalAction TernaryPoly.SymmetricSpaceRationalCharts

section Chart

variable (F : FrameOut)

/-- The part of the glued flat over the chart box. -/
def VO : Set FD := PiD ⁻¹' (embedding '' F.Tt)

/-- The chart point of a point of the glued flat over the chart box. -/
def kap (x : VO F) : F.UT pS :=
  (F.chartHomeo pS pS_isQuotientCovering).symm ⟨PiD x.1, x.2⟩

theorem continuous_kap : Continuous (kap F) := by
  unfold kap
  refine (F.chartHomeo pS pS_isQuotientCovering).symm.continuous.comp ?_
  exact Continuous.subtype_mk (continuous_PiD.comp continuous_subtype_val) _

/-- The chart point as a morphism. -/
def kapHom : TopCat.of (VO F) ⟶ TopCat.of ↥(F.UT pS) := TopCat.ofHom ⟨kap F, continuous_kap F⟩

theorem embedding_sec_kap (x : VO F) :
    embedding ((F.sec pS pS_isQuotientCovering).hom (kap F x)) = PiD x.1 := by
  have h := F.chartHomeo_val pS pS_isQuotientCovering (kap F x)
  have h2 : F.chartHomeo pS pS_isQuotientCovering (kap F x) = ⟨PiD x.1, x.2⟩ := by
    unfold kap; exact (F.chartHomeo pS pS_isQuotientCovering).apply_symm_apply _
  rw [h2] at h
  exact h.symm

theorem chartHom_kap : kapHom F ≫ F.chartHom pS pS_isQuotientCovering =
    sInclusion (VO F) ≫ PiHom := by
  ext x
  exact (embedding_sec_kap F x)

theorem diagSpace_congr {s s' t t' : ℝ} (hs : 0 < s) (ht : 0 < t) (hs' : 0 < s') (ht' : 0 < t')
    (h1 : s = s') (h2 : t = t') : diagSpace s t hs ht = diagSpace s' t' hs' ht' := by
  subst h1; subst h2; rfl

theorem chamber_pos (g : RationalGL) (q : ℝ × ℝ) (hs : 0 < q.1) (ht : 0 < q.2) :
    chamber g q = embedding (act (realRational g) (diagSpace q.1 q.2 hs ht)) := by
  have h1 : (clampH q.1).1 = q.1 := max_eq_left hs.le
  have h2 : (clampH q.2).1 = q.2 := max_eq_left ht.le
  change chamberH g (clampH q.1, clampH q.2) = _
  rw [chamberH_pos g _ (by simpa [h1] using hs) (by simpa [h2] using ht)]
  rw [diagSpace_congr _ _ hs ht h1 h2]

theorem VO_coords (x : VO F) :
    ∃ (k : Fin 6) (s t : ℝ), 0 < s ∧ s ≤ 1 ∧ 0 < t ∧ t ≤ 1 ∧ LamD x.1 = hexLam k (s, t) ∧
      rhoE (psi ((F.sec pS pS_isQuotientCovering).hom (kap F x))) =
        mk2 (hexM k 0 0 * Real.log s + hexM k 0 1 * Real.log t)
          (hexM k 1 0 * Real.log s + hexM k 1 1 * Real.log t) := by
  obtain ⟨y, hy⟩ := x
  induction y using Quot.ind with
  | mk d =>
  obtain ⟨k, ⟨q, hq⟩⟩ := d
  have hmem : PiD (Quot.mk _ (k, (⟨q, hq⟩ : SqT))) ∈ embedding '' F.Tt := hy
  have hrange : PiD (Quot.mk _ (k, (⟨q, hq⟩ : SqT))) ∈ Set.range embedding := by
    obtain ⟨S, -, hS⟩ := hmem
    exact ⟨S, hS⟩
  have hpos : 0 < q.1 ∧ 0 < q.2 := by
    by_contra hneg
    have : q.1 ≤ 0 ∨ q.2 ≤ 0 := by
      rw [not_and_or] at hneg
      push Not at hneg
      exact hneg
    exact fk_edge_not_interior k.val q this hrange
  refine ⟨k, q.1, q.2, hpos.1, hq.2.1, hpos.2, hq.2.2.2, rfl, ?_⟩
  have h1 := embedding_sec_kap F ⟨_, hy⟩
  have h2 : PiD (Quot.mk _ (k, (⟨q, hq⟩ : SqT))) =
      embedding (act (realRational (hexW k.val)) (diagSpace q.1 q.2 hpos.1 hpos.2)) :=
    chamber_pos (hexW k.val) q hpos.1 hpos.2
  have h3 : (F.sec pS pS_isQuotientCovering).hom (kap F ⟨_, hy⟩) =
      act (realRational (hexW k.val)) (diagSpace q.1 q.2 hpos.1 hpos.2) :=
    embedding_isOpenEmbedding.isEmbedding.injective (h1.trans h2)
  rw [h3]
  exact rho_chamber k q.1 q.2 hpos.1 hpos.2

end Chart

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
