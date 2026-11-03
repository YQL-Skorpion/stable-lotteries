import OptimalG.Certificates.CubicSupport
import OptimalG.Certificates.HighAssembly

/-! Exact local evaluation of assembled pieces. The open left endpoint avoids
requiring an arbitrary tie convention; continuity recovers both closed endpoints. -/
namespace OptimalG.Certificates
open Set

def cubicLookupCheck (p : CubicPiece) : List CubicPiece → Bool
  | [] => false
  | q::qs => if p=q then true else decide (q.hi≤p.lo) && cubicLookupCheck p qs

theorem cubicLookupCheck_values {p : CubicPiece} {ps : List CubicPiece}
    (hc : cubicLookupCheck p ps=true) (L S : ℝ) {r : ℝ}
    (hr : r∈Ioc (p.lo:ℝ) (p.hi:ℝ)) :
    cubicScore L ps r=p.score (r-p.lo) ∧
      cubicPrimitive L S ps r=p.primitive (r-p.lo) ∧
      cubicSlope ps r=p.slope (r-p.lo) := by
  induction ps with
  | nil => simp [cubicLookupCheck] at hc
  | cons q qs ih =>
    unfold cubicLookupCheck at hc
    split at hc
    next he =>
      subst q
      simp only [cubicScore,cubicPrimitive,cubicSlope,if_pos hr.2]
      trivial
    next he =>
      have hh : q.hi≤p.lo ∧ cubicLookupCheck p qs=true := by
        simpa only [Bool.and_eq_true,decide_eq_true_eq] using hc
      have hqp : (q.hi:ℝ)≤p.lo := by exact_mod_cast hh.1
      have hqr : ¬r≤q.hi := by linarith [hr.1]
      simpa only [cubicScore,cubicPrimitive,cubicSlope,if_neg hqr] using ih hh.2

theorem cubicLookupCheck_closed_values {p : CubicPiece} {ps : List CubicPiece}
    (hc : cubicLookupCheck p ps=true) (hp : p.lo<p.hi) (L S : ℝ)
    (hs : Continuous (cubicScore L ps)) (hf : Continuous (cubicPrimitive L S ps))
    {r : ℝ} (hr : r∈Icc (p.lo:ℝ) (p.hi:ℝ)) :
    cubicScore L ps r=p.score (r-p.lo) ∧ cubicPrimitive L S ps r=p.primitive (r-p.lo) := by
  have hlt : (p.lo:ℝ)<p.hi := by exact_mod_cast hp
  have he1 : EqOn (cubicScore L ps) (fun t => p.score (t-p.lo)) (Ioo (p.lo:ℝ) p.hi) :=
    fun t ht => (cubicLookupCheck_values hc L S ⟨ht.1,ht.2.le⟩).1
  have he2 : EqOn (cubicPrimitive L S ps) (fun t => p.primitive (t-p.lo)) (Ioo (p.lo:ℝ) p.hi) :=
    fun t ht => (cubicLookupCheck_values hc L S ⟨ht.1,ht.2.le⟩).2.1
  have hps : Continuous (fun t : ℝ => p.score (t-p.lo)) :=
    (continuous_iff_continuousAt.mpr (fun t => (p.score_hasDerivAt t).continuousAt)).comp
      (continuous_id.sub continuous_const)
  have hpf : Continuous (fun t : ℝ => p.primitive (t-p.lo)) :=
    (continuous_iff_continuousAt.mpr (fun t => (p.primitive_hasDerivAt t).continuousAt)).comp
      (continuous_id.sub continuous_const)
  have hh : r∈closure (Ioo (p.lo:ℝ) p.hi) := by rwa [closure_Ioo hlt.ne]
  exact ⟨he1.closure hs hps hh,he2.closure hf hpf hh⟩

end OptimalG.Certificates
