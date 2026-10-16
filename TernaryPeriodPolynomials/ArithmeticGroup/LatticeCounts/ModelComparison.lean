module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.AdelicValue
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.RightTranslation
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.ReductionProof
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Equivariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarSlash

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof

variable {σ : CuspidalRepresentation} {n : ℕ}

theorem atFinite_mul' (A B : BinaryFiniteGL) : atFinite (A * B) = atFinite A * atFinite B := by
  show combineGL 1 (A * B) = combineGL 1 A * combineGL 1 B
  rw [← combineGL_mul, one_mul]

/-- Right translation by an integral finite matrix fixes the realization of a spherical vector. -/
theorem realize_mul_integral (I : EichlerInput σ n) (x : BinaryAdelicGL)
    (k : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    σ.realize I.vector (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) =
      σ.realize I.vector x := by
  have fixed : σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) I.vector.val =
      I.vector.val := I.vector_spherical k
  have sub : (⟨σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) I.vector.val,
      σ.smooth_stable _ I.vector.val I.vector.property⟩ : σ.smooth) = I.vector :=
    Subtype.ext fixed
  rw [← σ.equivariant _ I.vector x, sub]

/-- The realization of the scalar-weighted model at a positive-determinant real matrix is the
Hecke section `F_h`, with no extra factor. -/
theorem realize_atInfinity_eq_Fh (I : EichlerInput σ n) (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (g : BinaryRealGL) (hg : 0 < (GeneralLinearGroup.det g).val) :
    σ.realize I.vector (atInfinity g) = Fh (-2 * I.halfWeight) ⇑h g := by
  have pos := cuspScalarWeightedRealization_positive σ I.central_positive I.halfWeight I.vector
    I.rotation g hg UpperHalfPlane.I
  have hv : h (g • UpperHalfPlane.I) =
      cuspScalarWeightedRealization σ I.halfWeight I.vector 1 ((g • UpperHalfPlane.I : UpperHalfPlane) : ℂ) :=
    congrFun hform (g • UpperHalfPlane.I)
  rw [← cuspScalarWeightedRealization_I σ I.halfWeight I.vector (atInfinity g)]
  rw [show (UpperHalfPlane.I : ℂ) = Complex.I from rfl] at pos
  unfold Fh Nf
  rw [pos, hv, GeneralLinearGroup.val_det_apply,
    show ((-2 * I.halfWeight : ℤ) : ℂ) / 2 = ((-I.halfWeight : ℤ) : ℂ) by push_cast; ring,
    Complex.cpow_intCast, show -(-2 * I.halfWeight) = 2 * I.halfWeight by ring]


open Classical in
/-- Realization of a Hilbert vector, zero off the smooth vectors. -/
def smoothReal (σ : CuspidalRepresentation) (w : σ.H) : BinaryAdelicGL → ℂ :=
  if hw : w ∈ σ.smooth then σ.realize ⟨w, hw⟩ else 0

theorem smoothReal_eq_realize (σ : CuspidalRepresentation) (w : σ.H) (hw : w ∈ σ.smooth) :
    smoothReal σ w = σ.realize ⟨w, hw⟩ := by
  unfold smoothReal
  rw [dite_eq_left hw]

/-- The model value at a positive-determinant point, for any lattice reduction `L` of `gf`. -/
theorem vhModel_realize_eq_of_reduction (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hgInf : 0 < (GeneralLinearGroup.det gInf).val)
    (gf : BinaryFiniteGL) (L : LatticeReduction gf) :
    smoothReal σ (σ.π (atFinite gf) I.vector.val) (atInfinity gInf) =
      Fh (-2 * I.halfWeight) ⇑h (binaryRationalReal L.γ * gInf) := by
  have hdetR : 0 < (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ)).val := by
    have e : (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ)).val =
        algebraMap ℚ ℝ (GeneralLinearGroup.det L.γ).val := by
      simp only [GeneralLinearGroup.val_det_apply]
      exact (RingHom.map_det (algebraMap ℚ ℝ) _).symm
    rw [e, eq_ratCast]
    exact Rat.cast_pos.mpr L.det_pos
  have hdet : 0 < (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ * gInf)).val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos hdetR hgInf
  have hint := L.integral
  rw [binaryIntegralFinite, MonoidHom.mem_range] at hint
  obtain ⟨k, hk⟩ := hint
  have comm : ∀ f : BinaryFiniteGL, atFinite f * atInfinity gInf = atInfinity gInf * atFinite f :=
    fun f => (atInfinity_commute_atFinite gInf f).eq.symm
  have prod : (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ) *
      atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) L.γ)) *
      (atInfinity gInf * atFinite gf) =
      atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ * gInf) *
        atFinite (GeneralLinearGroup.map integralEmbedding k) := by
    rw [hk]
    calc (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ) *
          atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) L.γ)) *
          (atInfinity gInf * atFinite gf)
        = atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ) *
          ((atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) L.γ) * atInfinity gInf) *
            atFinite gf) := by simp only [mul_assoc]
      _ = atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ) *
          ((atInfinity gInf * atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) L.γ)) *
            atFinite gf) := by rw [comm]
      _ = (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ) * atInfinity gInf) *
          (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) L.γ) * atFinite gf) := by
          simp only [mul_assoc]
      _ = atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) L.γ * gInf) *
          atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) L.γ * gf) := by
          rw [atInfinity_mul, atFinite_mul']
  rw [smoothReal_eq_realize σ _ (σ.smooth_stable _ I.vector.val I.vector.property),
    σ.equivariant (atFinite gf) I.vector (atInfinity gInf),
    ← σ.leftRational L.γ I.vector (atInfinity gInf * atFinite gf),
    binaryRationalMatrix_split L.γ, prod, realize_mul_integral I _ k,
    realize_atInfinity_eq_Fh I h hform _ hdet]
  rfl

/-- **The literal model-versus-classical comparison** (formerly the named comparison
`VhModelComparison`), for an Eichler input `I` whose vector realizes `h` and a positive-determinant
archimedean component. The finite section `π(ι_p A) v_h` evaluated at `gInf` is `v_h(gInf, ι_p A)`,
with no extra normalization factor. -/
theorem vhModel_eq (I : EichlerInput σ n) (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (p : FinitePlace) (A : GeneralLinearGroup (Fin 2) (p.adicCompletion ℚ))
    (gInf : BinaryRealGL) (hgInf : 0 < (GeneralLinearGroup.det gInf).val) :
    smoothReal σ (σ.π (atFinite (ιGL p A)) I.vector.val) (atInfinity gInf) =
      vhValue (-2 * I.halfWeight) h gInf (ιGL p A) := by
  rw [vhValue_eq_of_reduction (-2 * I.halfWeight) h gInf hgInf (ιGL p A)
    (Classical.choice (latticeReductionExists (ιGL p A)))]
  exact vhModel_realize_eq_of_reduction I h hform gInf hgInf (ιGL p A) _

end TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
