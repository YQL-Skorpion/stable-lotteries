import OptimalG.Certificates.AffineBox

/-! Affine feature boxes retain the shared mass dependence of node coefficients. -/
namespace OptimalG.Certificates

 def RatVector4.residual (v s : RatVector4) (r : ℚ) : RatVector4 :=
  ⟨v.x0-s.x0*r,v.x1-s.x1*r,v.x2-s.x2*r,v.x3-s.x3*r⟩

structure SegmentBox4 where
  parameter : RatInterval
  slopes : RatVector4
  residuals : RatBox4
  deriving DecidableEq, Repr

namespace SegmentBox4

def Contains (b : SegmentBox4) (v : RatVector4) (r : ℚ) : Prop :=
  b.parameter.lo≤r ∧ r≤b.parameter.hi ∧ b.residuals.Contains (v.residual b.slopes r)
instance (b : SegmentBox4) (v : RatVector4) (r : ℚ) : Decidable (b.Contains v r) :=
  inferInstanceAs (Decidable (_ ∧ _))
def containsCheck (b : SegmentBox4) (v : RatVector4) (r : ℚ) : Bool := decide (b.Contains v r)

def shiftBox (residual : RatInterval) (s t : ℚ) (parameter : RatInterval) : RatInterval :=
  residual.add ((RatInterval.point (s-t)).mul parameter)

def subsetCheck (a b : SegmentBox4) : Bool := a.parameter.subsetCheck b.parameter &&
  ((shiftBox a.residuals.b0 a.slopes.x0 b.slopes.x0 a.parameter).subsetCheck b.residuals.b0 &&
  ((shiftBox a.residuals.b1 a.slopes.x1 b.slopes.x1 a.parameter).subsetCheck b.residuals.b1 &&
  ((shiftBox a.residuals.b2 a.slopes.x2 b.slopes.x2 a.parameter).subsetCheck b.residuals.b2 &&
   (shiftBox a.residuals.b3 a.slopes.x3 b.slopes.x3 a.parameter).subsetCheck b.residuals.b3)))

private theorem shift_sound {a b parameter : RatInterval} {v r s t : ℚ}
    (hp : parameter.lo≤r ∧ r≤parameter.hi) (hv : a.lo≤v-s*r ∧ v-s*r≤a.hi)
    (hc : (shiftBox a s t parameter).subsetCheck b=true) : b.lo≤v-t*r ∧ v-t*r≤b.hi := by
  have hr : parameter.Contains (r:ℝ) := ⟨by exact_mod_cast hp.1,by exact_mod_cast hp.2⟩
  have ha : a.Contains ((v-s*r:ℚ):ℝ) := ⟨by exact_mod_cast hv.1,by exact_mod_cast hv.2⟩
  have hh := RatInterval.add_contains ha (RatInterval.mul_contains (RatInterval.point_contains (s-t)) hr)
  have he : ((v-s*r:ℚ):ℝ)+((s-t:ℚ):ℝ)*(r:ℝ)=((v-t*r:ℚ):ℝ) := by push_cast; ring
  rw [he] at hh
  have hb := RatInterval.subsetCheck_contains hh hc
  exact ⟨by exact_mod_cast hb.1,by exact_mod_cast hb.2⟩

theorem subsetCheck_contains {a b : SegmentBox4} {v : RatVector4} {r : ℚ}
    (ha : a.Contains v r) (hc : a.subsetCheck b=true) : b.Contains v r := by
  have hh : a.parameter.subsetCheck b.parameter=true ∧
      (shiftBox a.residuals.b0 a.slopes.x0 b.slopes.x0 a.parameter).subsetCheck b.residuals.b0=true ∧
      (shiftBox a.residuals.b1 a.slopes.x1 b.slopes.x1 a.parameter).subsetCheck b.residuals.b1=true ∧
      (shiftBox a.residuals.b2 a.slopes.x2 b.slopes.x2 a.parameter).subsetCheck b.residuals.b2=true ∧
      (shiftBox a.residuals.b3 a.slopes.x3 b.slopes.x3 a.parameter).subsetCheck b.residuals.b3=true := by
    simpa only [subsetCheck,Bool.and_eq_true] using hc
  have hpar : b.parameter.lo≤a.parameter.lo ∧ a.parameter.hi≤b.parameter.hi := of_decide_eq_true hh.1
  rcases ha with ⟨hl,hu,h0,h1,h2,h3,h4,h5,h6,h7⟩
  have hb0 := shift_sound ⟨hl,hu⟩ ⟨h0,h1⟩ hh.2.1
  have hb1 := shift_sound ⟨hl,hu⟩ ⟨h2,h3⟩ hh.2.2.1
  have hb2 := shift_sound ⟨hl,hu⟩ ⟨h4,h5⟩ hh.2.2.2.1
  have hb3 := shift_sound ⟨hl,hu⟩ ⟨h6,h7⟩ hh.2.2.2.2
  exact ⟨hpar.1.trans hl,hu.trans hpar.2,hb0.1,hb0.2,hb1.1,hb1.2,hb2.1,hb2.2,hb3.1,hb3.2⟩

def interval (b : SegmentBox4) (f : Affine4) : RatInterval :=
  (f.interval b.residuals).add ((RatInterval.point
    (f.k0*b.slopes.x0+f.k1*b.slopes.x1+f.k2*b.slopes.x2+f.k3*b.slopes.x3)).mul b.parameter)

def lowerCheck (b : SegmentBox4) (f : Affine4) : Bool := decide (0≤(b.interval f).lo)

theorem interval_sound {b : SegmentBox4} {f : Affine4} {v : RatVector4} {r : ℚ}
    (hb : b.Contains v r) : (b.interval f).Contains (f.eval v) := by
  have hr : b.parameter.Contains (r:ℝ) := ⟨by exact_mod_cast hb.1,by exact_mod_cast hb.2.1⟩
  have h := RatInterval.add_contains (Affine4.interval_sound (f:=f) hb.2.2)
    (RatInterval.mul_contains (RatInterval.point_contains
      (f.k0*b.slopes.x0+f.k1*b.slopes.x1+f.k2*b.slopes.x2+f.k3*b.slopes.x3)) hr)
  have he : (f.eval (v.residual b.slopes r):ℝ)+
      ((f.k0*b.slopes.x0+f.k1*b.slopes.x1+f.k2*b.slopes.x2+f.k3*b.slopes.x3:ℚ):ℝ)*(r:ℝ)=
      (f.eval v:ℝ) := by
    simp only [Affine4.eval,RatVector4.residual,Rat.cast_add,Rat.cast_sub,Rat.cast_mul]
    ring
  rw [he] at h
  exact h

theorem lowerCheck_sound {b : SegmentBox4} {f : Affine4} {v : RatVector4} {r : ℚ}
    (hc : b.lowerCheck f=true) (hb : b.Contains v r) : 0≤f.eval v := by
  have hh : (0:ℚ)≤(b.interval f).lo := of_decide_eq_true hc
  have hlo : (0:ℝ)≤(b.interval f).lo := by exact_mod_cast hh
  have h := hlo.trans (interval_sound hb).1
  exact_mod_cast h

end SegmentBox4
end OptimalG.Certificates
