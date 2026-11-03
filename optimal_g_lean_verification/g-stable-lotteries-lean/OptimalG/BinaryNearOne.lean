import OptimalG.SigmaPrimitive
import OptimalG.PolynomialCompletion
import OptimalG.BinaryHighRanks

/-! C.18 for every mass sufficiently near one. A finite lower rectangle sum
at width .02 covers the only remaining rank strip; all other ranks and all
smaller widths are handled analytically. -/
namespace OptimalG
open Set MeasureTheory

/-- A lower sum for an antitone continuous function. The sample values may
come from independently certified rational lower bounds. -/
theorem antitone_right_sum_le_integral {sigma lower : ℝ → ℝ} {q H : ℝ}
    {n : ℕ} {cuts : ℕ → ℝ} (hH : 0≤H)
    (hcont : ContinuousOn sigma (Icc q (q+H)))
    (hanti : AntitoneOn sigma (Icc q (q+H)))
    (hzero : cuts 0=q) (hend : cuts n=q+H)
    (hcuts : ∀ i≤n,cuts i ∈ Icc q (q+H))
    (hstep : ∀ i<n,cuts i≤cuts (i+1))
    (hlower : ∀ i<n,lower (cuts (i+1))≤sigma (cuts (i+1))) :
    ∑ i ∈ Finset.range n,(cuts (i+1)-cuts i)*lower (cuts (i+1))≤∫ r in q..q+H,sigma r := by
  have hi (i : ℕ) (hin : i<n) : IntervalIntegrable sigma volume (cuts i) (cuts (i+1)) :=
    (hcont.mono (Icc_subset_Icc (hcuts i hin.le).1 (hcuts (i+1) (by omega)).2)).intervalIntegrable_of_Icc
      (hstep i hin)
  have hs : ∀ i<n,(cuts (i+1)-cuts i)*lower (cuts (i+1))≤∫ r in cuts i..cuts (i+1),sigma r := by
    intro i hin
    have hh := intervalIntegral.integral_mono_on (hstep i hin)
      (intervalIntegrable_const (c:=lower (cuts (i+1)))) (hi i hin) (by
        intro r hr
        exact (hlower i hin).trans (hanti
          ⟨(hcuts i hin.le).1.trans hr.1,hr.2.trans (hcuts (i+1) (by omega)).2⟩
          (hcuts (i+1) (by omega)) hr.2))
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  have hh := Finset.sum_le_sum (s:=Finset.range n) (fun i hi => hs i (Finset.mem_range.mp hi))
  rw [intervalIntegral.sum_integral_adjacent_intervals hi,hzero,hend] at hh
  exact hh

noncomputable def binaryKappa (phi : ℝ → ℝ) (d : ℝ) : ℝ :=
  (d-curvePrimitive phi (1-d)/(1-d))/d^2

/-- The normalized tail coefficient is affine after multiplication by 1-d. -/
theorem binaryKappa_polynomial {phi : ℝ → ℝ} {z Y H d : ℝ}
    (hz : z≠1) (hd : d≠0) (hd1 : d≠1)
    (htail : curvePrimitive phi (1-d)=tailPrimitive z Y H (1-d)) :
    binaryKappa phi d=(tailBackwardSlope z Y H/2-1-tailBackwardCurvature z Y H*d/3)/(1-d) := by
  unfold binaryKappa
  rw [htail,tailPrimitive_backward z Y H (1-d) hz]
  simp only [sub_sub_cancel]
  have hh : 1-d≠0 := sub_ne_zero.mpr hd1.symm
  field_simp
  ring

/-- Two scalar tail-coefficient bounds control κ at every smaller width. -/
theorem binaryKappa_polynomial_upper {phi : ℝ → ℝ} {z Y H d B : ℝ}
    (hz : z≠1) (hd : d ∈ Ioo (0:ℝ) 1)
    (htail : curvePrimitive phi (1-d)=tailPrimitive z Y H (1-d))
    (hB : tailBackwardSlope z Y H/2-1≤B)
    (hdec : tailBackwardSlope z Y H/2-1≤tailBackwardCurvature z Y H/3) :
    binaryKappa phi d≤B := by
  rw [binaryKappa_polynomial hz hd.1.ne' (ne_of_lt hd.2) htail]
  apply le_trans _ hB
  apply (div_le_iff₀ (sub_pos.mpr hd.2)).mpr
  have hh := mul_le_mul_of_nonneg_right hdec hd.1.le
  nlinarith only [hh]

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- The small-rank near-one tests follow from one actual score value. -/
theorem nearOne_binary_low_ranks {d q B : ℝ}
    (hd : d ∈ Ioc (0:ℝ) (1/50:ℝ)) (hq : q ∈ Icc (0:ℝ) (1/4:ℝ))
    (hB : 0≤B) (hql : q≤lam)
    (hanti : AntitoneOn (scoreDefect phi lam) (Icc (0:ℝ) (27/100:ℝ)))
    (hk : binaryKappa phi d≤B)
    (hcheck : B*lam≤50*scoreDefect phi lam (27/100)+1/2) :
    q+((1-d)/curvePrimitive phi (1-d))*packingDelta phi (1-d) q≤lam := by
  have hd1 : d<1 := by linarith [hd.2]
  have hqd : q+d≤27/100 := by linarith [hq.2,hd.2]
  have hs0 := h.scoreDefect_nonneg (r:=27/100) ⟨by norm_num,by norm_num⟩
  have hi := intervalIntegral.integral_mono_on (μ:=volume) (show q≤q+d by linarith [hd.1])
    (intervalIntegrable_const (c:=scoreDefect phi lam (27/100)))
    ((h.scoreDefect_continuous.mono (Icc_subset_Icc hq.1 (by linarith))).intervalIntegrable_of_Icc
      (by linarith [hd.1])) (by
        intro r hr
        exact hanti ⟨hq.1.trans hr.1,hr.2.trans hqd⟩ ⟨by norm_num,le_rfl⟩ (hr.2.trans hqd))
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hi
  have hscaled : 50*scoreDefect phi lam (27/100)≤
      (∫ r in q..q+d,scoreDefect phi lam r)/d^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hd.1)).mpr
    have hh := mul_le_mul_of_nonneg_left hd.2 hs0
    have hh' := mul_le_mul_of_nonneg_left hh hd.1.le
    nlinarith only [hi,hh']
  apply h.nearOne_binary_of_normalized hd.1 hd1 hq.1 (by linarith)
  have hm := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hql)
  have hqB := mul_nonneg hB hq.1
  change _-binaryKappa phi d*(lam-q)+1/2≥0
  nlinarith only [hscaled,hm,hqB,hcheck]

/-- Above rank .337, the nonnegative slack integral alone is sufficient. -/
theorem nearOne_binary_high_low_ranks {d q B : ℝ}
    (hd : d ∈ Ioo (0:ℝ) 1) (hq : q ∈ Icc (337/1000:ℝ) lam) (hqd : q+d≤1)
    (hB : 0≤B) (hk : binaryKappa phi d≤B)
    (hcheck : B*(lam-337/1000)≤1/2) :
    q+((1-d)/curvePrimitive phi (1-d))*packingDelta phi (1-d) q≤lam := by
  have hq0 : 0≤q := by linarith [hq.1]
  have hi := intervalIntegral.integral_nonneg (μ:=volume) (show q≤q+d by linarith [hd.1])
    (fun r hr => h.scoreDefect_nonneg ⟨hq0.trans hr.1,hr.2.trans hqd⟩)
  have hdiv := div_nonneg hi (sq_nonneg d)
  have hm := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hq.2)
  have hBq := mul_le_mul_of_nonneg_left (show lam-q≤lam-337/1000 by linarith [hq.1]) hB
  apply h.nearOne_binary_of_normalized hd.1 hd.2 hq0 hqd
  change _-binaryKappa phi d*(lam-q)+1/2≥0
  linarith only [hdiv,hm,hBq,hcheck]

/-- A finite certified lower sum at the single width .02 handles every
smaller width for the remaining rank strip. -/
theorem nearOne_binary_of_lower_sum {d q B : ℝ} {lower : ℝ → ℝ}
    {n : ℕ} {cuts : ℕ → ℝ}
    (hd : d ∈ Ioc (0:ℝ) (1/50:ℝ)) (hq : q ∈ Icc (1/4:ℝ) (337/1000:ℝ))
    (hql : q≤lam)
    (hanti : AntitoneOn (scoreDefect phi lam) (Icc q (q+1/50)))
    (hk : binaryKappa phi d≤B)
    (hzero : cuts 0=q) (hend : cuts n=q+1/50)
    (hcuts : ∀ i≤n,cuts i ∈ Icc q (q+1/50))
    (hstep : ∀ i<n,cuts i≤cuts (i+1))
    (hlower : ∀ i<n,lower (cuts (i+1))≤scoreDefect phi lam (cuts (i+1)))
    (hcheck : 0≤2500*(∑ i ∈ Finset.range n,(cuts (i+1)-cuts i)*lower (cuts (i+1)))-B*(lam-q)+1/2) :
    q+((1-d)/curvePrimitive phi (1-d))*packingDelta phi (1-d) q≤lam := by
  have hq0 : 0≤q := by linarith [hq.1]
  have hqH : q+1/50≤1 := by linarith [hq.2]
  have hi := antitone_right_sum_le_integral (by norm_num : (0:ℝ)≤1/50)
    (h.scoreDefect_continuous.mono (Icc_subset_Icc hq0 hqH)) hanti hzero hend hcuts hstep hlower
  apply h.nearOne_binary_of_endpoint hd (by linarith [hd.2]) hq0 hql hqH hanti hk
  norm_num
  nlinarith only [hi,hcheck]

/-- Equal-width right samples eliminate all partition premises from the
finite endpoint certificate. -/
theorem nearOne_binary_of_uniform_lower_sum {d q B : ℝ} {lower : ℝ → ℝ}
    {n : ℕ} (hn : 0<n)
    (hd : d ∈ Ioc (0:ℝ) (1/50:ℝ)) (hq : q ∈ Icc (1/4:ℝ) (337/1000:ℝ))
    (hql : q≤lam)
    (hanti : AntitoneOn (scoreDefect phi lam) (Icc q (q+1/50)))
    (hk : binaryKappa phi d≤B)
    (hlower : ∀ r ∈ Icc q (q+1/50),lower r≤scoreDefect phi lam r)
    (hcheck : 0≤2500*(∑ i ∈ Finset.range n,(1/(50*(n:ℝ)))*lower (q+((i:ℝ)+1)/(50*(n:ℝ))))-
      B*(lam-q)+1/2) :
    q+((1-d)/curvePrimitive phi (1-d))*packingDelta phi (1-d) q≤lam := by
  let cuts : ℕ → ℝ := fun i => q+(i:ℝ)/(50*(n:ℝ))
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hden : (0:ℝ)<50*(n:ℝ) := by positivity
  have hcuts : ∀ i≤n,cuts i ∈ Icc q (q+1/50) := by
    intro i hi
    have hiR : (i:ℝ)≤n := by exact_mod_cast hi
    constructor
    · dsimp [cuts]
      linarith only [div_nonneg (Nat.cast_nonneg i) hden.le]
    · dsimp [cuts]
      have hh := (div_le_div_of_nonneg_right hiR hden.le)
      have he : (n:ℝ)/(50*(n:ℝ))=1/50 := by field_simp
      rw [he] at hh
      linarith only [hh]
  have hend : cuts n=q+1/50 := by dsimp [cuts]; congr 1; field_simp
  have hstep : ∀ i<n,cuts i≤cuts (i+1) := by
    intro i hi
    dsimp [cuts]
    gcongr
    exact_mod_cast Nat.le_succ i
  have hdiff (i : ℕ) : cuts (i+1)-cuts i=1/(50*(n:ℝ)) := by
    dsimp [cuts]
    push_cast
    ring
  apply h.nearOne_binary_of_lower_sum hd hq hql hanti hk
    (by simp [cuts]) hend hcuts hstep
    (fun i hi => hlower (cuts (i+1)) (hcuts (i+1) (by omega)))
  simp only [hdiff]
  simpa only [cuts,Nat.cast_add,Nat.cast_one] using hcheck

/-- The entire near-one range follows from a finite lower-sum inequality on
q∈[.25,.337] at width .02, two scalar checks, and the actual tail κ bound. -/
theorem binary_near_one_all {lower : ℝ → ℝ} {B : ℝ} {n : ℕ}
    (hn : 0<n) (hlam : lam ∈ Icc (1/2:ℝ) (3/5:ℝ))
    (hc : ConcaveOn ℝ (Icc lam 1) phi) (hB : 0≤B)
    (hanti : AntitoneOn (scoreDefect phi lam) (Icc (0:ℝ) (31/40:ℝ)))
    (hk : ∀ d ∈ Ioc (0:ℝ) (1/50:ℝ),binaryKappa phi d≤B)
    (hlower : ∀ r ∈ Icc (1/4:ℝ) (357/1000:ℝ),lower r≤scoreDefect phi lam r)
    (hlowCheck : B*lam≤50*lower (27/100)+1/2)
    (hhighCheck : B*(lam-337/1000)≤1/2)
    (hcheck : ∀ q ∈ Icc (1/4:ℝ) (337/1000:ℝ),
      0≤2500*(∑ i ∈ Finset.range n,(1/(50*(n:ℝ)))*lower (q+((i:ℝ)+1)/(50*(n:ℝ))))-
        B*(lam-q)+1/2) :
    ∀ p ∈ Ico (49/50:ℝ) 1,∀ q ∈ Icc (0:ℝ) p,normalizedBinaryTest phi p q≤lam := by
  intro p hp
  have hp0 : p ∈ Ioo (0:ℝ) 1 := ⟨by linarith only [hp.1],hp.2⟩
  have hd : 1-p ∈ Ioc (0:ℝ) (1/50:ℝ) := ⟨by linarith only [hp.2],by linarith only [hp.1]⟩
  apply h.binary_all_splits_of_low hc hlam.1 hp0
  intro q hq hqp hql
  have hq1 : q+(1-p)≤1 := by linarith only [hqp]
  have hgoal : q+(p/curvePrimitive phi p)*packingDelta phi p q≤lam := by
    by_cases hqlo : q≤1/4
    · have hs := hlower (27/100) ⟨by norm_num,by norm_num⟩
      have hh := h.nearOne_binary_low_ranks hd ⟨hq,hqlo⟩ hB hql
        (hanti.mono (Icc_subset_Icc le_rfl (by norm_num))) (hk (1-p) hd)
        (by linarith only [hlowCheck,hs])
      simpa only [sub_sub_cancel] using hh
    · by_cases hqhi : 337/1000≤q
      · have hh := h.nearOne_binary_high_low_ranks ⟨hd.1,by linarith only [hd.2]⟩
          ⟨hqhi,hql⟩ hq1 hB (hk (1-p) hd) hhighCheck
        simpa only [sub_sub_cancel] using hh
      · have hqb : q ∈ Icc (1/4:ℝ) (337/1000:ℝ) := ⟨le_of_not_ge hqlo,le_of_not_ge hqhi⟩
        have hh := h.nearOne_binary_of_uniform_lower_sum hn hd hqb hql
          (hanti.mono (Icc_subset_Icc hq (by linarith only [hqb.2]))) (hk (1-p) hd)
          (fun r hr => hlower r ⟨hqb.1.trans hr.1,by linarith only [hr.2,hqb.2]⟩)
          (hcheck q hqb)
        simpa only [sub_sub_cancel] using hh
  exact hgoal

end VerifierCurve
end OptimalG
