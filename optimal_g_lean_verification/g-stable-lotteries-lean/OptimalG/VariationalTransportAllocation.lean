import OptimalG.VariationalTransportSource
import OptimalG.VariationalTransportTerms
import OptimalG.VariationalPushforwardSum

/-! Exact allocation of the four logarithmic terms to the two rank maps.
Zero early r-terms can be removed before constructing the cropped rank-density
partition, preserving the actual integral rather than extending the rank cover
with an artificial contributor. -/
namespace OptimalG.Variational
open Set MeasureTheory Real Certificates.Transport

 theorem transport_four_allocation (rho w : ℝ) (a0 : Fin 4→ℝ)
    (xiR xiA : ℝ) (test : ℝ→ℝ) :
    rho*(∑ i,referenceWeight (a0 i) (transportDelta i) w*test (transportXi xiR xiA i))=
      (rho*(referenceWeight (a0 0) (transportDelta 0) w+
        referenceWeight (a0 2) (transportDelta 2) w))*test xiR+
      (rho*(referenceWeight (a0 1) (transportDelta 1) w+
        referenceWeight (a0 3) (transportDelta 3) w))*test xiA := by
  simp [Fin.sum_univ_succ,transportXi]
  ring

theorem transportDerivativeSource_allocation (rho w0 : ℝ→ℝ) (a0 : ℝ→Fin 4→ℝ)
    (xiR xiA : ℝ→ℝ) (s : ℝ) :
    transportDerivativeSource rho w0 a0 (fun t=>transportXi (xiR t) (xiA t)) transportDelta s=
      (rho s*(referenceWeight (a0 s 0) (transportDelta 0) (w0 s)+
        referenceWeight (a0 s 2) (transportDelta 2) (w0 s)))*(xiR s-1)+
      (rho s*(referenceWeight (a0 s 1) (transportDelta 1) (w0 s)+
        referenceWeight (a0 s 3) (transportDelta 3) (w0 s)))*(xiA s-1) := by
  exact transport_four_allocation (rho s) (w0 s) (a0 s) (xiR s) (xiA s) (·-1)

theorem transportEntropySource_allocation (rho w0 : ℝ→ℝ) (a0 : ℝ→Fin 4→ℝ)
    (xiR xiA : ℝ→ℝ) (s : ℝ) :
    transportEntropySource rho w0 a0 (fun t=>transportXi (xiR t) (xiA t)) transportDelta s=
      (rho s*(referenceWeight (a0 s 0) (transportDelta 0) (w0 s)+
        referenceWeight (a0 s 2) (transportDelta 2) (w0 s)))*transportEntropy (xiR s)+
      (rho s*(referenceWeight (a0 s 1) (transportDelta 1) (w0 s)+
        referenceWeight (a0 s 3) (transportDelta 3) (w0 s)))*transportEntropy (xiA s) := by
  exact transport_four_allocation (rho s) (w0 s) (a0 s) (xiR s) (xiA s) transportEntropy

theorem early_r_allocation_zero (L M S z r a R j mA rho w : ℝ) :
    rho*(referenceWeight (earlyLogCoefficients L M S z r a R j mA 0) (transportDelta 0) w+
      referenceWeight (earlyLogCoefficients L M S z r a R j mA 2) (transportDelta 2) w)=0 := by
  simp [earlyLogCoefficients,referenceWeight]

theorem pushforwardDensity_filter_zero (segments : List ReferenceSegment)
    (rank : ReferenceNode→ℚ) (weight : ReferenceSegment→ℝ→ℝ)
    (keep : ReferenceSegment→Bool)
    (hzero : ∀ seg∈segments,keep seg=false→∀ t,weight seg t=0) (r : ℝ) :
    pushforwardDensity (segments.filter keep) rank weight r=
      pushforwardDensity segments rank weight r := by
  induction segments with
  | nil => rfl
  | cons seg rest ih =>
    have hi := ih (fun s hs=>hzero s (List.mem_cons_of_mem seg hs))
    cases hk : keep seg
    · have hz : segmentDensity seg rank (weight seg) r=0 := by
        simp only [segmentDensity,hzero seg List.mem_cons_self hk,zero_div,ite_self]
      simpa only [List.filter_cons,hk,Bool.false_eq_true,↓reduceIte,
        pushforwardDensity,List.map_cons,List.sum_cons,hz,zero_add] using hi
    · simpa only [List.filter_cons,hk,↓reduceIte,pushforwardDensity,List.map_cons,
        List.sum_cons] using congrArg (fun x=>segmentDensity seg rank (weight seg) r+x) hi

/-- A cropped support statement allows a genuine zero weight on an omitted
segment. It does not pretend that the omitted affine rank image lies inside
the central matching interval. -/
theorem pushforwardDensity_zero_outside_or_zero (segments : List ReferenceSegment)
    (rank : ReferenceNode→ℚ) (weight : ReferenceSegment→ℝ→ℝ) {a b r : ℝ}
    (himage : ∀ seg∈segments,(∀ t,weight seg t=0) ∨
      (a≤(rank seg.left:ℝ) ∧ (rank seg.right:ℝ)≤b))
    (hr : r∉Icc a b) : pushforwardDensity segments rank weight r=0 := by
  unfold pushforwardDensity
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨seg,hs,rfl⟩ := List.mem_map.mp hv
  rcases himage seg hs with hz | hi
  · simp only [segmentDensity,hz,zero_div,ite_self]
  · have hout : r∉Ioo (rank seg.left:ℝ) (rank seg.right:ℝ) := by
      intro hh
      exact hr ⟨hi.1.trans hh.1.le,hh.2.le.trans hi.2⟩
    exact if_neg hout

theorem pushforwardDensity_cropped_setIntegral (segments : List ReferenceSegment)
    (rank : ReferenceNode→ℚ) (weight : ReferenceSegment→ℝ→ℝ) (test : ℝ→ℝ) {a b : ℝ}
    (himage : ∀ seg∈segments,(∀ t,weight seg t=0) ∨
      (a≤(rank seg.left:ℝ) ∧ (rank seg.right:ℝ)≤b)) :
    (∫ r,pushforwardDensity segments rank weight r*test r)=
      ∫ r in Icc a b,pushforwardDensity segments rank weight r*test r := by
  rw [←integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with r
  by_cases hr : r∈Icc a b
  · simp only [indicator_of_mem hr]
  · rw [indicator_of_notMem hr,
      pushforwardDensity_zero_outside_or_zero segments rank weight himage hr,zero_mul]

end OptimalG.Variational
