import OptimalG.Certificates.RoundedProgram

/-! Exact affine bounds over four-dimensional rational feature boxes. -/
namespace OptimalG.Certificates

structure RatVector4 where
  x0 : ℚ
  x1 : ℚ
  x2 : ℚ
  x3 : ℚ
  deriving DecidableEq, Repr

structure RatBox4 where
  b0 : RatInterval
  b1 : RatInterval
  b2 : RatInterval
  b3 : RatInterval
  deriving DecidableEq, Repr

namespace RatBox4

def Contains (b : RatBox4) (v : RatVector4) : Prop :=
  b.b0.lo≤v.x0 ∧ v.x0≤b.b0.hi ∧ b.b1.lo≤v.x1 ∧ v.x1≤b.b1.hi ∧
    b.b2.lo≤v.x2 ∧ v.x2≤b.b2.hi ∧ b.b3.lo≤v.x3 ∧ v.x3≤b.b3.hi
instance (b : RatBox4) (v : RatVector4) : Decidable (b.Contains v) := inferInstanceAs (Decidable (_ ∧ _))

def containsCheck (b : RatBox4) (v : RatVector4) : Bool := decide (b.Contains v)
def subsetCheck (a b : RatBox4) : Bool := a.b0.subsetCheck b.b0 &&
  (a.b1.subsetCheck b.b1 && (a.b2.subsetCheck b.b2 && a.b3.subsetCheck b.b3))

theorem subsetCheck_contains {a b : RatBox4} {v : RatVector4}
    (ha : a.Contains v) (hc : a.subsetCheck b=true) : b.Contains v := by
  have hh : (b.b0.lo≤a.b0.lo ∧ a.b0.hi≤b.b0.hi) ∧
      (b.b1.lo≤a.b1.lo ∧ a.b1.hi≤b.b1.hi) ∧
      (b.b2.lo≤a.b2.lo ∧ a.b2.hi≤b.b2.hi) ∧
      (b.b3.lo≤a.b3.lo ∧ a.b3.hi≤b.b3.hi) := by
    simpa only [subsetCheck,RatInterval.subsetCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
  rcases ha with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  exact ⟨hh.1.1.trans h0,h1.trans hh.1.2,hh.2.1.1.trans h2,h3.trans hh.2.1.2,
    hh.2.2.1.1.trans h4,h5.trans hh.2.2.1.2,hh.2.2.2.1.trans h6,h7.trans hh.2.2.2.2⟩

end RatBox4

structure Affine4 where
  offset : ℚ
  k0 : ℚ
  k1 : ℚ
  k2 : ℚ
  k3 : ℚ
  deriving DecidableEq, Repr

namespace Affine4

def add (f g : Affine4) : Affine4 :=
  ⟨f.offset+g.offset,f.k0+g.k0,f.k1+g.k1,f.k2+g.k2,f.k3+g.k3⟩
def scale (k : ℚ) (f : Affine4) : Affine4 :=
  ⟨k*f.offset,k*f.k0,k*f.k1,k*f.k2,k*f.k3⟩
def eval (f : Affine4) (v : RatVector4) : ℚ :=
  f.offset+f.k0*v.x0+f.k1*v.x1+f.k2*v.x2+f.k3*v.x3

def interval (f : Affine4) (b : RatBox4) : RatInterval :=
  ((((RatInterval.point f.offset).add ((RatInterval.point f.k0).mul b.b0)).add
    ((RatInterval.point f.k1).mul b.b1)).add ((RatInterval.point f.k2).mul b.b2)).add
      ((RatInterval.point f.k3).mul b.b3)

def lowerCheck (f : Affine4) (b : RatBox4) : Bool := decide (0≤(f.interval b).lo)

@[simp] theorem eval_add (f g : Affine4) (v : RatVector4) : (f.add g).eval v=f.eval v+g.eval v := by
  unfold add eval
  ring

@[simp] theorem eval_scale (k : ℚ) (f : Affine4) (v : RatVector4) : (f.scale k).eval v=k*f.eval v := by
  unfold scale eval
  ring

theorem interval_sound {f : Affine4} {b : RatBox4} {v : RatVector4}
    (hb : b.Contains v) : (f.interval b).Contains (f.eval v) := by
  rcases hb with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  have hc0 : b.b0.Contains (v.x0:ℝ) := ⟨by exact_mod_cast h0,by exact_mod_cast h1⟩
  have hc1 : b.b1.Contains (v.x1:ℝ) := ⟨by exact_mod_cast h2,by exact_mod_cast h3⟩
  have hc2 : b.b2.Contains (v.x2:ℝ) := ⟨by exact_mod_cast h4,by exact_mod_cast h5⟩
  have hc3 : b.b3.Contains (v.x3:ℝ) := ⟨by exact_mod_cast h6,by exact_mod_cast h7⟩
  have h := RatInterval.add_contains (RatInterval.add_contains (RatInterval.add_contains
    (RatInterval.add_contains (RatInterval.point_contains f.offset)
      (RatInterval.mul_contains (RatInterval.point_contains f.k0) hc0))
      (RatInterval.mul_contains (RatInterval.point_contains f.k1) hc1))
      (RatInterval.mul_contains (RatInterval.point_contains f.k2) hc2))
      (RatInterval.mul_contains (RatInterval.point_contains f.k3) hc3)
  simpa only [interval,eval,Rat.cast_add,Rat.cast_mul] using h

theorem lowerCheck_sound {f : Affine4} {b : RatBox4} {v : RatVector4}
    (hc : f.lowerCheck b=true) (hb : b.Contains v) : 0≤f.eval v := by
  have hh : (0:ℚ)≤(f.interval b).lo := of_decide_eq_true hc
  have hreal : (0:ℝ)≤(f.interval b).lo := by exact_mod_cast hh
  have h := hreal.trans (interval_sound hb).1
  exact_mod_cast h

end Affine4
end OptimalG.Certificates
