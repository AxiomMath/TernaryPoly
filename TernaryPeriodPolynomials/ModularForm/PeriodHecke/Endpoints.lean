module

public import TernaryPeriodPolynomials.ModularForm.PeriodHecke.Transfer
public import TernaryPeriodPolynomials.ModularForm.Symbol.Full

@[expose] public section


noncomputable section
open Complex Matrix Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod BinaryCuspHeckeEndomorphism BinaryRationalHeckePrime BinaryModularSymbol

/-- The actual coefficient-and-point action has the corresponding actual rational-cusp endpoint. -/
theorem primitiveAction_tendsto {d : ℕ} (f : Forms d) (L : Line) (v : Coordinates)
    (g : GL2) (hg : 0 < g⁻¹.det.val) :
    Tendsto (fun t : ℝ => primitiveAction f g v
      (rationalMobius (slRational (cuspChart L)) (I*t))) atTop
      (𝓝 (functionAction g (endpoint f (lineAction g⁻¹ L)) v)) := by
  let w := ((complexify g)⁻¹).val.mulVec v
  have hp : 0 < (g⁻¹*slRational (cuspChart L)).det.val := by
    simpa only [map_mul, Units.val_mul, slRational_det, mul_one] using hg
  have hL : lineAction (g⁻¹*slRational (cuspChart L)) infinity = lineAction g⁻¹ L := by
    rw [lineAction_mul, cuspChart_spec]
  have h := (endpoint_tendsto f (lineAction g⁻¹ L) w (g⁻¹*slRational (cuspChart L)) hp hL).const_mul
    (g.det.val : ℂ)⁻¹
  simpa only [w, primitiveAction, functionAction_apply, rationalMobius_mul] using h

/-- Passing the genuine primitive identity to every rational cusp yields exact endpoint transfer. -/
theorem endpoint_hecke {d : ℕ} (f : Forms d) (p : ℕ) [Fact p.Prime] (L : Line) (v : Coordinates) :
    endpoint (T d p f) L v = (p : ℂ)^(d+1) * ∑ i : PrimeIndex p,
      functionAction (adjugateRepresentative p i)
        (endpoint f (lineAction (adjugateRepresentative p i)⁻¹ L)) v := by
  have h₁ := endpoint_tendsto (T d p f) L v (slRational (cuspChart L))
    (by rw [slRational_det]; norm_num) (cuspChart_spec L)
  have h₂ := (tendsto_finsetSum Finset.univ (fun i _ =>
    primitiveAction_tendsto f L v (adjugateRepresentative p i) (adjugate_inv_det_pos p i))).const_mul
      ((p : ℂ)^(d+1))
  apply tendsto_nhds_unique h₁
  apply h₂.congr
  intro t
  exact (eichlerIntegral_hecke_transfer f p v (rationalMobius_im_pos _ _)).symm

/-- Exact transfer on each actual oriented modular symbol, with the p^(d+1) factor. -/
theorem full_symbol_hecke {d : ℕ} (f : Forms d) (p : ℕ) [Fact p.Prime] (L M : Line) :
    full (T d p f) (symbol L M) = (p : ℚ)^(d+1) •
      ∑ i : PrimeIndex p, homAction functionAction (adjugateRepresentative p i) (full f) (symbol L M) := by
  funext v
  rw [full_symbol, endpoint_hecke, endpoint_hecke, ←mul_sub]
  simp only [Finset.sum_apply, homAction_apply, action_symbol, functionAction_apply, full_symbol,
    ←Finset.sum_sub_distrib, mul_sub, Pi.smul_apply, Algebra.smul_def, map_pow, map_natCast]

/-- Actual full holomorphic symbols intertwine the genuine standard cusp operator with the
literal adjugate prime transfer, before the determinant-negative odd projection. -/
theorem full_hecke {d : ℕ} (f : Forms d) (p : ℕ) [Fact p.Prime] :
    full (T d p f) = (p : ℚ)^(d+1) •
      ∑ i : PrimeIndex p, homAction functionAction (adjugateRepresentative p i) (full f) := by
  apply LinearMap.ext
  intro c
  have hc : c ∈ Submodule.span ℚ (Set.range (symbol infinity)) := by rw [span_symbols]; trivial
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨M,rfl⟩ := hc
    simpa only [LinearMap.smul_apply, LinearMap.sum_apply] using full_symbol_hecke f p infinity M
  | zero => simp
  | add c d _ _ hc hd => simp only [map_add, hc, hd]
  | smul q c _ hc => simp only [map_smul, hc]

end TernaryPoly.BinaryCuspSymbol
