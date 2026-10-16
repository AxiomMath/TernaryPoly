module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.AwayCompressionStable
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.GlobalLocal

@[expose] public section


/-!
# The away compression scalar

Integrating the plane cusp lift over the opposite radical with coordinates away from `∞` and `3`
multiplies the cusp vector at an argument that is integral away from three by a scalar `awayLam`
that depends only on the inducing data and the parameter, not on the section or the argument.

For each coordinate `u` the Iwasawa decomposition `n⁻(u) = n · m(s, B) · κ` with `κ ∈ GL₃(Ẑ^{(3)})`
shows that the cusp lift at `n⁻(u) y` is `c(s, B) • π(B)` of the cusp lift at `y`. Its norm is a fixed
multiple of the norm at `y`, and its compression to the `GL₂(Ẑ^{(3)})`-fixed vectors is
`c(s, B) ω(B)` times the vector at `y`. The scalar `awayLam` is the integral of the second quantity
when the first is integrable, and zero otherwise. The integral of the cusp lifts is fixed by
`GL₂(Ẑ^{(3)})` because that group preserves the measure and conjugates the opposite radical.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

section Abstract

open Classical in
/-- A function whose compression is a scalar multiple of a fixed vector and whose norm is a fixed
multiple of the norm of that vector integrates to the scalar multiple given by the integrals of the
scalars, when the norms are integrable, and to zero otherwise. -/
theorem integral_eq_lam_smul {X H : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (P : H →L[ℂ] H)
    (φ : X → H) (hφ : AEStronglyMeasurable φ μ) (w : H) (ν : X → ℝ) (Λ : X → ℂ)
    (hnorm : ∀ u, ‖φ u‖ = ν u * ‖w‖) (hproj : ∀ u, P (φ u) = Λ u • w)
    (hfix : Integrable φ μ → P (∫ u, φ u ∂μ) = ∫ u, φ u ∂μ) :
    (∫ u, φ u ∂μ) = (if Integrable ν μ then ∫ u, Λ u ∂μ else 0) • w := by
  by_cases hw : w = 0
  · have h0 : ∀ u, φ u = 0 := fun u => by
      have h := hnorm u
      rw [hw, norm_zero, mul_zero] at h
      exact norm_eq_zero.mp h
    have hfun : φ = fun _ => 0 := funext h0
    rw [hfun, hw, smul_zero]
    simp
  · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    by_cases hint : Integrable ν μ
    · rw [ite_eq_left hint]
      have hφint : Integrable φ μ := by
        refine Integrable.mono' (hint.mul_const ‖w‖) hφ (Filter.Eventually.of_forall fun u => ?_)
        exact (hnorm u).le
      have hP := hfix hφint
      calc ∫ u, φ u ∂μ = P (∫ u, φ u ∂μ) := hP.symm
        _ = ∫ u, P (φ u) ∂μ := (P.integral_comp_comm hφint).symm
        _ = ∫ u, Λ u • w ∂μ := by simp only [hproj]
        _ = (∫ u, Λ u ∂μ) • w := integral_smul_const _ _
    · rw [ite_eq_right hint, zero_smul]
      apply integral_undef
      intro hφint
      apply hint
      have h1 : Integrable (fun u => ‖φ u‖ / ‖w‖) μ := hφint.norm.div_const ‖w‖
      refine h1.congr (Filter.Eventually.of_forall fun u => ?_)
      change ‖φ u‖ / ‖w‖ = ν u
      rw [hnorm u, mul_div_assoc, div_self hwpos.ne', mul_one]

end Abstract

section Cusp

variable {degree : ℕ} (data : InducingData degree) (parameter : ℂ)

/-- The scalar by which the cusp lift is multiplied under a plane Levi element. -/
def awayCoefficient (s : Adelesˣ) (B : BinaryAdelicGL) : ℂ :=
  data.chi.toMonoidHom s * normPower s (-2 * inductionExponent .plane parameter) *
    normPower (GeneralLinearGroup.det B) (binaryInductionExponent degree .plane parameter)

theorem cuspVector_parabolic (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (a b : Adeles) (s : Adelesˣ)
    (B : BinaryAdelicGL) (h : AdelicGL) :
    (CuspLift.vector data .plane parameter function induced
      (planeUnipotent a b * (planeLevi 1 s * planeLevi B 1) * h)).val =
      awayCoefficient data parameter s B •
        data.cusp.π B (CuspLift.vector data .plane parameter function induced h).val := by
  unfold awayCoefficient
  have hb : (CuspLift.vector data .plane parameter function induced (planeLevi B 1 * h)).val =
      normPower (GeneralLinearGroup.det B) (binaryInductionExponent degree .plane parameter) •
        data.cusp.π B (CuspLift.vector data .plane parameter function induced h).val :=
    CuspLiftCovariance.vector_binary data .plane parameter function induced B h
  rw [mul_assoc, CuspLiftCovariance.vector_plane_radical, mul_assoc,
    CuspLiftCovariance.vector_plane_rankOne, Submodule.coe_smul, hb, smul_smul]

theorem cuspVector_awayOpposite (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) {y : AdelicGL} (hy : AwayStable y)
    {u : FiniteAwayThree × FiniteAwayThree} {a b : Adeles} {s : Adelesˣ} {Bf : BinaryFiniteGL}
    {κ : FiniteGL} (hκ : κ ∈ awayCompact)
    (hdec : awayOpposite u =
      planeUnipotent a b * (planeLevi 1 s * planeLevi (atFinite Bf) 1) * atFinite κ) :
    (CuspLift.vector data .plane parameter function induced (awayOpposite u * y)).val =
      awayCoefficient data parameter s (atFinite Bf) •
        data.cusp.π (atFinite Bf) (CuspLift.vector data .plane parameter function induced y).val := by
  obtain ⟨κ', hκ', hcomm⟩ := hy κ hκ
  have h1 : awayOpposite u * y =
      (planeUnipotent a b * (planeLevi 1 s * planeLevi (atFinite Bf) 1) * y) * atFinite κ' := by
    rw [hdec, mul_assoc _ (atFinite κ) y, hcomm, ← mul_assoc]
  have hfi : CuspLift.vector data .plane parameter function induced
      ((planeUnipotent a b * (planeLevi 1 s * planeLevi (atFinite Bf) 1) * y) * atFinite κ') =
      CuspLift.vector data .plane parameter function induced
        (planeUnipotent a b * (planeLevi 1 s * planeLevi (atFinite Bf) 1) * y) :=
    CuspLift.finite_invariant data .plane parameter function induced _
      ⟨κ', awayCompact_mem_finiteLevel hκ'⟩
  rw [h1, hfi]
  exact cuspVector_parabolic data parameter function induced a b s (atFinite Bf) y

theorem vector_mem_fixed (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) {y : AdelicGL} (hy : AwayStable y) :
    (CuspLift.vector data .plane parameter function induced y).val ∈
      fixedVectors data.cusp HeckeEigen.Satake.K3 := by
  rintro ⟨_, ⟨m, hm, rfl⟩⟩
  change data.cusp.π (atFinite m) (CuspLift.vector data .plane parameter function induced y).val = _
  obtain ⟨k', hk', hcomm⟩ := hy (planeLevi m 1) (planeLevi_mem_awayCompact hm)
  have hb : (CuspLift.vector data .plane parameter function induced
      (planeLevi (atFinite m) 1 * y)).val =
      normPower (GeneralLinearGroup.det (atFinite m)) (binaryInductionExponent degree .plane parameter) •
        data.cusp.π (atFinite m) (CuspLift.vector data .plane parameter function induced y).val :=
    CuspLiftCovariance.vector_binary data .plane parameter function induced (atFinite m) y
  rw [HeckeEigen.np_det_spherical hm.2, one_smul] at hb
  rw [← hb, ← HeckeEigen.atFinite_planeLevi, hcomm]
  exact congrArg Subtype.val (CuspLift.finite_invariant data .plane parameter function induced y
    ⟨k', awayCompact_mem_finiteLevel hk'⟩)

theorem starProjection_pi (σ : CuspidalRepresentation) {B : BinaryFiniteGL}
    (hB : B ∈ awayGroup placeThree) {w : σ.H} (hw : w ∈ fixedVectors σ HeckeEigen.Satake.K3) :
    (fixedVectors σ HeckeEigen.Satake.K3).starProjection (σ.π (atFinite B) w) =
      HeckeEigen.Satake.omega σ B • w := by
  have h := congrArg Subtype.val (HeckeEigen.Satake.omega_spec σ hB ⟨w, hw⟩)
  rw [compression_coe] at h
  exact h

/-- The data of the cusp lifts at the opposite radical coordinate `u`: for every induced section and
every stable argument, the norm is `nu` times the norm at the argument and the compression to the
`GL₂(Ẑ^{(3)})`-fixed vectors is `lam` times the vector at the argument. -/
def AwayProfile (u : FiniteAwayThree × FiniteAwayThree) (lam : ℂ) (nu : ℝ) : Prop :=
  ∀ (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function) (y : AdelicGL),
    AwayStable y →
      ‖(CuspLift.vector data .plane parameter function induced (awayOpposite u * y)).val‖ =
          nu * ‖(CuspLift.vector data .plane parameter function induced y).val‖ ∧
      (fixedVectors data.cusp HeckeEigen.Satake.K3).starProjection
          (CuspLift.vector data .plane parameter function induced (awayOpposite u * y)).val =
        lam • (CuspLift.vector data .plane parameter function induced y).val

theorem exists_awayProfile (u : FiniteAwayThree × FiniteAwayThree) :
    ∃ (lam : ℂ) (nu : ℝ), AwayProfile data parameter u lam nu := by
  obtain ⟨a, b, s, Bf, κ, hκ, hBf, hdec⟩ := awayOpposite_iwasawa u
  refine ⟨awayCoefficient data parameter s (atFinite Bf) * HeckeEigen.Satake.omega data.cusp Bf,
    ‖awayCoefficient data parameter s (atFinite Bf)‖, ?_⟩
  intro function induced y hy
  have hv := cuspVector_awayOpposite data parameter function induced hy hκ hdec
  have hw := vector_mem_fixed data parameter function induced hy
  constructor
  · rw [hv, norm_smul, data.cusp.unitary]
  · rw [hv, map_smul, starProjection_pi data.cusp hBf hw, smul_smul]

/-- A choice of the norm factor and the compression factor at each opposite radical coordinate. -/
def awayProfileValue (u : FiniteAwayThree × FiniteAwayThree) : ℂ × ℝ :=
  Classical.epsilon (fun p : ℂ × ℝ => AwayProfile data parameter u p.1 p.2)

def awayLambda (u : FiniteAwayThree × FiniteAwayThree) : ℂ :=
  (awayProfileValue data parameter u).1

def awayNu (u : FiniteAwayThree × FiniteAwayThree) : ℝ :=
  (awayProfileValue data parameter u).2

theorem awayProfile_spec (u : FiniteAwayThree × FiniteAwayThree) :
    AwayProfile data parameter u (awayLambda data parameter u) (awayNu data parameter u) := by
  obtain ⟨lam, nu, h⟩ := exists_awayProfile data parameter u
  exact Classical.epsilon_spec
    (p := fun p : ℂ × ℝ => AwayProfile data parameter u p.1 p.2) ⟨(lam, nu), h⟩

open Classical in
/-- **The away compression scalar**: the integral of the compression factors when the norm factors are
integrable, and zero otherwise. -/
def awayLam : ℂ :=
  if Integrable (awayNu data parameter) awayRadicalMeasure then
    ∫ u, awayLambda data parameter u ∂awayRadicalMeasure
  else 0

theorem pi_atFinite_awayVector (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) {y : AdelicGL} (hy : AwayStable y)
    {m : BinaryFiniteGL} (hm : m ∈ awayLevel placeThree) (u : FiniteAwayThree × FiniteAwayThree) :
    data.cusp.π (atFinite m)
        (CuspLift.vector data .plane parameter function induced (awayOpposite u * y)).val =
      (CuspLift.vector data .plane parameter function induced
        (awayOpposite (awayRowAction m⁻¹ u) * y)).val := by
  obtain ⟨k', hk', hcomm⟩ := hy (planeLevi m 1) (planeLevi_mem_awayCompact hm)
  have hb : (CuspLift.vector data .plane parameter function induced
      (planeLevi (atFinite m) 1 * (awayOpposite u * y))).val =
      normPower (GeneralLinearGroup.det (atFinite m)) (binaryInductionExponent degree .plane parameter) •
        data.cusp.π (atFinite m) (CuspLift.vector data .plane parameter function induced
          (awayOpposite u * y)).val :=
    CuspLiftCovariance.vector_binary data .plane parameter function induced (atFinite m)
      (awayOpposite u * y)
  rw [HeckeEigen.np_det_spherical hm.2, one_smul] at hb
  rw [← hb, ← HeckeEigen.atFinite_planeLevi, ← mul_assoc, atFinite_planeLevi_mul_awayOpposite,
    mul_assoc, hcomm, ← mul_assoc]
  exact congrArg Subtype.val (CuspLift.finite_invariant data .plane parameter function induced _
    ⟨k', awayCompact_mem_finiteLevel hk'⟩)

theorem integral_mem_fixed (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) {y : AdelicGL} (hy : AwayStable y)
    (hint : Integrable (fun u => (CuspLift.vector data .plane parameter function induced
      (awayOpposite u * y)).val) awayRadicalMeasure) :
    (∫ u, (CuspLift.vector data .plane parameter function induced
      (awayOpposite u * y)).val ∂awayRadicalMeasure) ∈
        fixedVectors data.cusp HeckeEigen.Satake.K3 := by
  rintro ⟨_, ⟨m, hm, rfl⟩⟩
  change data.cusp.π (atFinite m) _ = _
  have h1 := (cuspOperator data.cusp (atFinite m)).integral_comp_comm hint
  simp only [cuspOperator_apply] at h1
  rw [← h1]
  simp only [pi_atFinite_awayVector data parameter function induced hy hm]
  exact integral_awayRowAction (sphericalFinite.inv_mem hm.2)
    (fun u => (CuspLift.vector data .plane parameter function induced (awayOpposite u * y)).val)

theorem awayOpposite_vector_continuous (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (y : AdelicGL) :
    Continuous (fun u : FiniteAwayThree × FiniteAwayThree =>
      (CuspLift.vector data .plane parameter function induced (awayOpposite u * y)).val) :=
  (CuspLift.continuous data .plane parameter function induced).comp
    (awayOpposite_continuous.mul continuous_const)

/-- **The away integral of the cusp lift is `awayLam` times the cusp lift at a stable argument.** -/
theorem awayIntegral_vector (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) {y : AdelicGL} (hy : AwayStable y) :
    (∫ u, (CuspLift.vector data .plane parameter function induced
      (awayOpposite u * y)).val ∂awayRadicalMeasure) =
        awayLam data parameter • (CuspLift.vector data .plane parameter function induced y).val :=
  integral_eq_lam_smul (fixedVectors data.cusp HeckeEigen.Satake.K3).starProjection
    (fun u => (CuspLift.vector data .plane parameter function induced (awayOpposite u * y)).val)
    (awayOpposite_vector_continuous data parameter function induced y).aestronglyMeasurable
    (CuspLift.vector data .plane parameter function induced y).val
    (awayNu data parameter) (awayLambda data parameter)
    (fun u => (awayProfile_spec data parameter u function induced y hy).1)
    (fun u => (awayProfile_spec data parameter u function induced y hy).2)
    (fun hint => Submodule.starProjection_eq_self_iff.mpr
      (integral_mem_fixed data parameter function induced hy hint))

/-- **Away compression in the form used by the global-local factorization.** -/
theorem awayIntegral_eq_smul_localIntegrand (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) {argument : AdelicGL}
    (hargument : AwayStable argument) (localParameter : LocalLine × LocalLine) :
    awayIntegral data parameter function induced argument localParameter =
      awayLam data parameter • localIntegrand data parameter function induced argument
        localParameter :=
  awayIntegral_vector data parameter function induced
    (awayStable_weyl_radical hargument localParameter)

/-- **The global Hilbert standard integral is `awayLam` times the local one.** -/
theorem standardValue_eq_awayLam_smul_localValue (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) {argument : AdelicGL}
    (hargument : AwayStable argument) :
    HilbertStandard.value data parameter function induced argument =
      awayLam data parameter • localValue data parameter function induced argument :=
  standardValue_eq_smul_localValue data parameter function induced halfPlane argument _
    (awayIntegral_eq_smul_localIntegrand data parameter function induced hargument)

theorem standardValue_eq_awayLam_smul_localValue_of_good (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) {argument : AdelicGL}
    (hargument : AwayGood argument) :
    HilbertStandard.value data parameter function induced argument =
      awayLam data parameter • localValue data parameter function induced argument :=
  standardValue_eq_awayLam_smul_localValue data parameter function induced halfPlane
    (awayStable_of_good hargument)

/-- Arguments whose finite part is integral at every place (the arguments of the local majorants). -/
theorem standardValue_eq_awayLam_smul_localValue_of_integral (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) {argument : AdelicGL}
    (hargument : ∃ integral : GeneralLinearGroup (Fin 3) IntegralAdeles,
      finiteGroup argument = GeneralLinearGroup.map integralEmbedding integral) :
    HilbertStandard.value data parameter function induced argument =
      awayLam data parameter • localValue data parameter function induced argument :=
  standardValue_eq_awayLam_smul_localValue_of_good data parameter function induced halfPlane
    (awayGood_of_integral hargument)

theorem standardValue_eq_awayLam_smul_localValue_of_maximalCompact (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) {argument : AdelicGL}
    (hargument : inMaximalCompact argument) :
    HilbertStandard.value data parameter function induced argument =
      awayLam data parameter • localValue data parameter function induced argument :=
  standardValue_eq_awayLam_smul_localValue_of_good data parameter function induced halfPlane
    (awayGood_of_inMaximalCompact hargument)

end Cusp

end TernaryPeriodPolynomials.EdgeConvergence
