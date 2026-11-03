import OptimalG.Certificates.CubicAssembly
import OptimalG.ConcaveGlue
import OptimalG.ConcaveIncrements

/-! A finite quadratic-score chain may have downward derivative jumps.
The checker proves concavity on the covered interval; it makes no assertion
about the arbitrary fallback score beyond the last endpoint. -/
namespace OptimalG.Certificates
open Set Filter
open scoped Topology

def quadraticConcaveLocal (p : CubicPiece) : Bool :=
  decide (p.lo<p.hi ∧ p.a3=0 ∧ p.a2≤0)

def quadraticConcaveJoin (p q : CubicPiece) : Bool :=
  decide (p.hi=q.lo ∧ p.scoreQ p.length=q.a0 ∧ q.a1≤p.slopeQ p.length)

def quadraticConcaveChainCheck (b : ℚ) : List CubicPiece → Bool
  | [] => false
  | [p] => quadraticConcaveLocal p && decide (p.hi=b)
  | p::q::ps => quadraticConcaveLocal p &&
      (quadraticConcaveJoin p q && quadraticConcaveChainCheck b (q::ps))

private theorem local_derivative (p : CubicPiece) (r : ℝ) :
    HasDerivAt (fun t => p.score (t-p.lo)) (p.slope (r-p.lo)) r := by
  simpa only [id_eq,mul_one,Function.comp_def] using
    (p.score_hasDerivAt (r-p.lo)).comp r ((hasDerivAt_id r).sub_const (p.lo:ℝ))

private theorem local_concavity {p : CubicPiece} (hp : quadraticConcaveLocal p=true)
    (a b : ℝ) : ConcaveOn ℝ (Icc a b) (fun t => p.score (t-p.lo)) := by
  have hh : p.lo<p.hi ∧ p.a3=0 ∧ p.a2≤0 := of_decide_eq_true hp
  have h2 : (p.a2:ℝ)≤0 := by exact_mod_cast hh.2.2
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc a b)
    (fun r _ => (local_derivative p r).continuousAt.continuousWithinAt)
    (fun r _ => (local_derivative p r).differentiableAt.differentiableWithinAt)
  intro r hr s hs hrs
  rw [(local_derivative p r).deriv,(local_derivative p s).deriv]
  have hm := mul_nonpos_of_nonpos_of_nonneg h2 (sub_nonneg.mpr hrs)
  simp only [CubicPiece.slope,hh.2.1,Rat.cast_zero,zero_mul,add_zero]
  nlinarith only [hm]

private theorem first_derivative {L : ℝ} {p : CubicPiece} {ps : List CubicPiece}
    (hp : p.lo<p.hi) : HasDerivAt (cubicScore L (p::ps)) (p.a1:ℝ) p.lo := by
  have hh : (p.lo:ℝ)<p.hi := by exact_mod_cast hp
  have hd := local_derivative p (p.lo:ℝ)
  norm_num [CubicPiece.slope] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hh] with r hr
  exact if_pos hr.le

/-- Downward jumps between adjacent score derivatives suffice for global
concavity of the explicitly assembled score. -/
theorem quadraticConcaveChainCheck_sound {b : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : quadraticConcaveChainCheck b (p::ps)=true) (L : ℝ) :
    (p.lo:ℝ)<b ∧ ConcaveOn ℝ (Icc (p.lo:ℝ) b) (cubicScore L (p::ps)) := by
  induction ps generalizing p with
  | nil =>
    have hh : quadraticConcaveLocal p=true ∧ p.hi=b := by
      simpa only [quadraticConcaveChainCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
    have hp : p.lo<p.hi ∧ p.a3=0 ∧ p.a2≤0 := of_decide_eq_true hh.1
    have hlen : (p.lo:ℝ)<b := by exact_mod_cast hh.2 ▸ hp.1
    refine ⟨hlen,(local_concavity hh.1 p.lo b).congr ?_⟩
    intro r hr
    exact (if_pos (by simpa only [hh.2] using hr.2)).symm
  | cons q qs ih =>
    have hh : quadraticConcaveLocal p=true ∧ quadraticConcaveJoin p q=true ∧
        quadraticConcaveChainCheck b (q::qs)=true := by
      simpa only [quadraticConcaveChainCheck,Bool.and_eq_true] using hc
    have hp : p.lo<p.hi ∧ p.a3=0 ∧ p.a2≤0 := of_decide_eq_true hh.1
    have hj : p.hi=q.lo ∧ p.scoreQ p.length=q.a0 ∧ q.a1≤p.slopeQ p.length :=
      of_decide_eq_true hh.2.1
    have hq : quadraticConcaveLocal q=true := by
      cases qs <;> simp only [quadraticConcaveChainCheck,Bool.and_eq_true] at hh <;>
        exact hh.2.2.1
    have hql : q.lo<q.hi ∧ q.a3=0 ∧ q.a2≤0 := of_decide_eq_true hq
    have ht := ih hh.2.2
    have hplo : (p.lo:ℝ)<p.hi := by exact_mod_cast hp.1
    have hpbe : (p.hi:ℝ)<b := by simpa only [hj.1] using ht.1
    have hjoin : p.score ((p.hi:ℝ)-p.lo)=cubicScore L (q::qs) p.hi := by
      have hv := congrArg (fun t:ℚ => (t:ℝ)) hj.2.1
      have hqhi : (q.lo:ℝ)≤q.hi := by exact_mod_cast hql.1.le
      simp only [hj.1,cubicScore,if_pos hqhi,sub_self,CubicPiece.score,
        mul_zero,zero_pow,add_zero]
      simpa [CubicPiece.length,hj.1,CubicPiece.score] using hv
    have hsl : (q.a1:ℝ)≤p.slope ((p.hi:ℝ)-p.lo) := by
      have hs := (Rat.cast_le (K:=ℝ)).mpr hj.2.2
      simpa [CubicPiece.length] using hs
    have hdq : HasDerivAt (cubicScore L (q::qs)) (q.a1:ℝ) p.hi := by
      simpa only [hj.1] using first_derivative (L:=L) (ps:=qs) hql.1
    refine ⟨hplo.trans hpbe,?_⟩
    exact concaveOn_joinAt hplo.le hpbe.le (local_concavity hh.1 p.lo p.hi)
      (by simpa only [hj.1] using ht.2) hjoin
      (local_derivative p p.hi).hasDerivWithinAt hdq.hasDerivWithinAt hsl

theorem quadraticConcaveChainCheck_tangent {b : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : quadraticConcaveChainCheck b (p::ps)=true) (L : ℝ)
    {r : ℝ} (hr : r∈Icc (p.lo:ℝ) b) :
    cubicScore L (p::ps) r≤(p.a0:ℝ)+p.a1*(r-p.lo) := by
  have hp : quadraticConcaveLocal p=true := by
    cases ps <;> simp only [quadraticConcaveChainCheck,Bool.and_eq_true] at hc <;> exact hc.1
  have hpl : p.lo<p.hi ∧ p.a3=0 ∧ p.a2≤0 := of_decide_eq_true hp
  have hplo : (p.lo:ℝ)≤p.hi := by exact_mod_cast hpl.1.le
  have hfirst : cubicScore L (p::ps) p.lo=(p.a0:ℝ) := by
    rw [cubicScore,if_pos hplo]
    simp [CubicPiece.score]
  rcases hr.1.eq_or_lt with he|hgt
  · subst r
    simp only [hfirst,sub_self,mul_zero,add_zero,le_refl]
  · have hh := (quadraticConcaveChainCheck_sound hc L).2.slope_le_of_hasDerivWithinAt
      ⟨le_rfl,(quadraticConcaveChainCheck_sound hc L).1.le⟩ hr hgt
      (first_derivative (ps:=ps) hpl.1).hasDerivWithinAt
    simp only [slope,vsub_eq_sub,smul_eq_mul,hfirst] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr hr.1)
    have hne : r-(p.lo:ℝ)≠0 := sub_ne_zero.mpr hgt.ne'
    rw [←mul_assoc,mul_inv_cancel₀ hne,one_mul] at hmul
    linarith only [hmul]

theorem quadraticConcaveChainCheck_increment {b : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : quadraticConcaveChainCheck b (p::ps)=true) (L : ℝ)
    {r s : ℝ} (hr : (p.lo:ℝ)≤r) (hrs : r≤s) (hs : s≤b) :
    cubicScore L (p::ps) s-cubicScore L (p::ps) r≤(p.a1:ℝ)*(s-r) := by
  have hh := quadraticConcaveChainCheck_sound hc L
  have hi := concave_increment_antitone hh.2
    (x:=(p.lo:ℝ)) (y:=r) (d:=s-r) ⟨le_rfl,hh.1.le⟩
    ⟨by linarith only [hr,hrs],by linarith only [hs]⟩ hr (sub_nonneg.mpr hrs)
  have ht := quadraticConcaveChainCheck_tangent hc L
    (r:=(p.lo:ℝ)+(s-r)) ⟨by linarith only [hrs],by linarith only [hr,hs]⟩
  have hp : quadraticConcaveLocal p=true := by
    cases ps <;> simp only [quadraticConcaveChainCheck,Bool.and_eq_true] at hc <;> exact hc.1
  have hpl : p.lo<p.hi ∧ p.a3=0 ∧ p.a2≤0 := of_decide_eq_true hp
  have hplo : (p.lo:ℝ)≤p.hi := by exact_mod_cast hpl.1.le
  have hfirst : cubicScore L (p::ps) p.lo=(p.a0:ℝ) := by
    rw [cubicScore,if_pos hplo]
    simp [CubicPiece.score]
  rw [hfirst,show r+(s-r)=s by ring] at hi
  nlinarith only [hi,ht]

end OptimalG.Certificates
