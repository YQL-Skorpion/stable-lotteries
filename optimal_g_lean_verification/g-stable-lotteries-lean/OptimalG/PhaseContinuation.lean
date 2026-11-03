import OptimalG.BoundedContinuation
import OptimalG.PhasePropagation
import OptimalG.PhaseStateGeometry

/-! Actual bounded continuation after a quantitative signed-field comparison. -/
namespace OptimalG.Variational
open Set
open scoped NNReal

theorem quadratic_state_bounds {lam z : ℝ}
    (hL : Certificates.Compact.LambdaRange lam) (hz : z ∈ Icc zStart zEnd) :
    -1 ≤ linePrimitive lam z-linePrimitive lam 1 ∧ linePrimitive lam z ≤ 1 := by
  have hz0 : 0 ≤ z := by norm_num [zStart,zEnd] at hz; linarith [hz.1]
  have hz1 : z ≤ 1 := by norm_num [zStart,zEnd] at hz; linarith [hz.2]
  have hL0 : 0 ≤ lam := by linarith [hL.1]
  have hL1 : lam ≤ 1 := by linarith [hL.2]
  have ha := mul_nonneg hL0 hz0
  have hb := mul_nonneg hz0 (sub_nonneg.mpr hz1)
  have hc := mul_nonneg (sub_nonneg.mpr hL1) hz0
  unfold linePrimitive
  constructor <;> nlinarith [sq_nonneg z]

/-- The comparison creates a genuine new trajectory on the whole interval;
the error subsolution remains in the fixed state truncation. -/
theorem exists_phase_continuation
    {lam S T gain mu : ℝ} (hL : Certificates.Compact.LambdaRange lam)
    (F G : ℝ → ℝ → ℝ) (K : ℝ≥0) (Y : ℝ → ℝ)
    (hmu : 0 ≤ mu) (hgain : mu ≤ gain) (hT : 0 ≤ T) (hST : T=S-gain)
    (hG : ∀ z, LipschitzWith K (G z))
    (htime : ∀ u, Continuous (fun z => G z u))
    (hY0 : Y zStart = linePrimitive lam zStart-S)
    (hYD : ∀ z ∈ Icc zStart zEnd,
      HasDerivWithinAt Y (F z (Y z)) (Icc zStart zEnd) z)
    (hYbounds : ∀ z ∈ Icc zStart zEnd,
      linePrimitive lam z-linePrimitive lam 1 ≤ Y z ∧ Y z ≤ linePrimitive lam z-S)
    (hfield : ∀ z ∈ Icc zStart zEnd,
      F z (Y z)-(6.19*mu+4.53*phaseError mu z) ≤ G z (Y z+gain-phaseError mu z))
    (hceiling : ∀ z u, G z u ≤ lam-z) :
    ∃ Z : ℝ → ℝ, Z zStart = linePrimitive lam zStart-T ∧
      (∀ z ∈ Icc zStart zEnd,
        HasDerivWithinAt Z (G z (Z z)) (Icc zStart zEnd) z) ∧
      ∀ z ∈ Icc zStart zEnd,
        Y z+gain-0.784*mu ≤ Z z ∧
        linePrimitive lam z-linePrimitive lam 1 ≤ Z z ∧ Z z ≤ linePrimitive lam z-T := by
  let W := fun z => Y z+gain-phaseError mu z
  let high := fun z => linePrimitive lam z-T
  have hYc : ContinuousOn Y (Icc zStart zEnd) := fun z hz => (hYD z hz).continuousWithinAt
  have hWc : ContinuousOn W (Icc zStart zEnd) :=
    (hYc.add continuousOn_const).sub (phaseError_continuous mu).continuousOn
  have hhighC : Continuous high := by unfold high linePrimitive; fun_prop
  have hhighD (z : ℝ) : HasDerivAt high (lam-z) z := by
    have hd := (((hasDerivAt_id z).const_mul lam).sub
      (((hasDerivAt_id z).pow 2).div_const 2)).sub_const T
    convert! hd using 1 <;> simp
  have hWd (z : ℝ) (hz : z ∈ Ico zStart zEnd) :
      HasDerivWithinAt W (F z (Y z)-(4.53*phaseError mu z+6.19*mu)) (Ici z) z := by
    have hd := (hYD z ⟨hz.1,hz.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hz)
    exact (hd.add_const gain).sub (phaseError_hasDerivAt mu z).hasDerivWithinAt
  have hWB (z : ℝ) (hz : z ∈ Icc zStart zEnd) :
      linePrimitive lam z-linePrimitive lam 1 ≤ W z ∧ W z ≤ high z := by
    have he := phaseError_bounds hmu hz
    have hb := hYbounds z hz
    dsimp [W,high]
    constructor <;> linarith [he.1,he.2,hb.1,hb.2]
  have hlowB (z : ℝ) (hz : z ∈ Icc zStart zEnd) : W z ∈ Icc (-1 : ℝ) 1 := by
    have hb := hWB z hz
    have hq := quadratic_state_bounds hL hz
    dsimp [high] at hb
    constructor <;> linarith [hb.1,hb.2,hq.1,hq.2]
  have hhighB (z : ℝ) (hz : z ∈ Icc zStart zEnd) : high z ∈ Icc (-1 : ℝ) 1 := by
    have hb := hWB z hz
    have hq := quadratic_state_bounds hL hz
    dsimp [high] at *
    constructor <;> linarith [hb.1,hb.2,hq.1,hq.2]
  have hinit : W zStart ≤ linePrimitive lam zStart-T ∧
      linePrimitive lam zStart-T ≤ high zStart := by
    rw [show W zStart=Y zStart+gain by simp [W,phaseError_start],hY0]
    dsimp [high]
    constructor <;> linarith
  obtain ⟨Z,hZ0,hZD,hZB⟩ := exists_continuation_between G K W high
    (fun z => F z (Y z)-(4.53*phaseError mu z+6.19*mu)) (fun z => lam-z)
    zStart zEnd (linePrimitive lam zStart-T) (by norm_num [zStart,zEnd])
    (fun z _ => hG z) (fun u => (htime u).continuousOn) hWc hhighC.continuousOn
    hWd (fun z _ => (hhighD z).hasDerivWithinAt)
    (fun z hz => by simpa only [W,add_comm (4.53*phaseError mu z)] using hfield z ⟨hz.1,hz.2.le⟩)
    (fun z _ => hceiling z (high z)) hlowB hhighB hinit
  refine ⟨Z,hZ0,hZD,?_⟩
  intro z hz
  have hb := hZB z hz
  have he := phaseError_bounds hmu hz
  have hw := hWB z hz
  dsimp [W,high] at hb hw
  exact ⟨by linarith [hb.1,he.2],by linarith [hw.1,hb.1],hb.2⟩

end OptimalG.Variational
