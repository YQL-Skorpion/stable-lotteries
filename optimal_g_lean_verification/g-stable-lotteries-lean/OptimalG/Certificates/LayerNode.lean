import OptimalG.Certificates.UpperRational

/-! Exact finite certificates for conservative layer-control coefficients. -/
namespace OptimalG.Certificates
open UpperProfileData

structure LayerNode where
  p : ℚ
  a : ℚ
  C : ℚ
  Cu : ℚ
  alphau : ℚ
  deriving DecidableEq, Repr

namespace LayerNode

def b (n : LayerNode) : ℚ := max n.a n.p
def R (n : LayerNode) : ℚ := UpperTrial.primitiveQ n.p
def P (n : LayerNode) : ℚ := lam*(1-n.p)-(1-n.p)^2/2-slack
def A (n : LayerNode) : ℚ := UpperTrial.scoreQ n.a
def B (n : LayerNode) : ℚ := UpperTrial.scoreQ n.b
def D (n : LayerNode) : ℚ := (2*lam-n.a)*n.R-(n.p+n.b-lam)*n.P
def alpha (n : LayerNode) : ℚ := (n.B+n.C*(n.p+n.b-lam))/n.R

def check (n : LayerNode) : Bool := decide
  ((1/4:ℚ)≤n.p ∧ n.p≤9/25 ∧ leftContact≤n.a ∧ 0<n.R ∧
    (if n.a=leftContact then (1/10:ℚ)≤n.C ∧ n.C≤-UpperTrial.slopeQ leftContact
      else n.C=-UpperTrial.slopeQ n.a) ∧
    n.R*n.A+n.P*n.B≤n.C*n.D ∧ n.C≤n.Cu ∧ n.alpha≤n.alphau)

/-- The checked rational coefficient supplies both global score supports. -/
theorem check_supports {n : LayerNode} (hc : n.check=true) {x y : ℝ}
    (hx : (0.28:ℝ)≤x) (hy : (0.28:ℝ)≤y) (hyp : (n.p:ℝ)≤y) :
    UpperTrial.score x+(n.C:ℝ)*x≤(n.A:ℝ)+(n.C:ℝ)*n.a ∧
    UpperTrial.score y+(n.C:ℝ)*y≤(n.B:ℝ)+(n.C:ℝ)*n.b := by
  have hh : (1/4:ℚ)≤n.p ∧ n.p≤9/25 ∧ leftContact≤n.a ∧ 0<n.R ∧
      (if n.a=leftContact then (1/10:ℚ)≤n.C ∧ n.C≤-UpperTrial.slopeQ leftContact
        else n.C=-UpperTrial.slopeQ n.a) ∧
      n.R*n.A+n.P*n.B≤n.C*n.D ∧ n.C≤n.Cu ∧ n.alpha≤n.alphau := of_decide_eq_true hc
  have ha : (leftContact:ℝ)≤n.a := by exact_mod_cast hh.2.2.1
  have hA : (n.A:ℝ)=UpperTrial.score n.a := by simp [A]
  have hB : (n.B:ℝ)=UpperTrial.score (max (n.a:ℝ) n.p) := by simp [B,b]
  have hb : (n.b:ℝ)=max (n.a:ℝ) n.p := by simp [b]
  rw [hA,hB,hb]
  by_cases he : n.a=leftContact
  · have hs : (1/10:ℚ)≤n.C ∧ n.C≤-UpperTrial.slopeQ leftContact := by
      simpa only [if_pos he] using hh.2.2.2.2.1
    have hlo : UpperTrial.slope leftContact≤-(n.C:ℝ) := by
      have hh' : (n.C:ℝ)≤-(UpperTrial.slopeQ leftContact:ℝ) := by exact_mod_cast hs.2
      rw [UpperTrial.slopeQ_cast] at hh'
      linarith
    have hhi : -(n.C:ℝ)≤-(0.1:ℝ) := by
      have hh' : ((1/10:ℚ):ℝ)≤n.C := by exact_mod_cast hs.1
      norm_num at hh' ⊢
      linarith
    have h1 := UpperTrial.contact_support hlo hhi hx
    have h2 := UpperTrial.contact_support_max hlo hhi hy hyp
    rw [he]
    constructor <;> nlinarith only [h1,h2]
  · have hs : n.C=-UpperTrial.slopeQ n.a := by simpa only [if_neg he] using hh.2.2.2.2.1
    have hC : (n.C:ℝ)=-UpperTrial.slope n.a := by
      have h := congrArg (fun q:ℚ => (q:ℝ)) hs
      simpa using h
    have h1 := UpperTrial.supporting_line ha hx
    have h2 := UpperTrial.supporting_line_max ha hy hyp
    rw [hC]
    constructor <;> nlinarith only [h1,h2]

/-- A checked node lower-bounds the entire independent-root control family at
its layer rank, under the explicit geometric sign hypotheses. -/
theorem check_lower {n : LayerNode} (hc : n.check=true) {U K x y : ℝ}
    (hU : 0≤U) (hK : 0≤K) (hx : (0.28:ℝ)≤x) (hy : (0.28:ℝ)≤y) (hyp : (n.p:ℝ)≤y)
    (hD : 0<Control.det (2*(lam:ℝ)-x) (n.p+y-lam) n.R n.P)
    (hcx : 0≤Control.cx U (n.p+y-lam) n.R K)
    (hcy : 0≤Control.cy U (2*(lam:ℝ)-x) n.P K) :
    -U*n.Cu-K*n.alphau≤Control.value U (2*(lam:ℝ)-x) (n.p+y-lam) n.R n.P K
      (UpperTrial.score x) (UpperTrial.score y) := by
  have hh : (1/4:ℚ)≤n.p ∧ n.p≤9/25 ∧ leftContact≤n.a ∧ 0<n.R ∧
      (if n.a=leftContact then (1/10:ℚ)≤n.C ∧ n.C≤-UpperTrial.slopeQ leftContact
        else n.C=-UpperTrial.slopeQ n.a) ∧
      n.R*n.A+n.P*n.B≤n.C*n.D ∧ n.C≤n.Cu ∧ n.alpha≤n.alphau := of_decide_eq_true hc
  have hR : (0:ℝ)<n.R := by exact_mod_cast hh.2.2.2.1
  have hs := check_supports hc hx hy hyp
  have hbal : (n.R:ℝ)*n.A+(n.P:ℝ)*n.B≤(n.C:ℝ)*
      Control.det (2*(lam:ℝ)-n.a) (n.p+n.b-lam) n.R n.P := by
    have h := congrArg (fun q:ℚ => (q:ℝ)) (show n.D=(2*lam-n.a)*n.R-(n.p+n.b-lam)*n.P from rfl)
    have hb : (n.R:ℝ)*n.A+(n.P:ℝ)*n.B≤(n.C:ℝ)*(n.D:ℝ) := by exact_mod_cast hh.2.2.2.2.2.1
    simpa [D,Control.det] using hb
  have hb := Control.lower_of_common_support U lam n.p n.R n.P K n.C n.a n.b n.A n.B x y
    (UpperTrial.score x) (UpperTrial.score y) hR hD hcx hcy hs.1 hs.2 hbal
  have ha : (n.alpha:ℝ)=((n.B:ℝ)+(n.C:ℝ)*(n.p+n.b-lam))/n.R := by simp [alpha]
  rw [← ha] at hb
  exact Control.lower_of_coefficient_enclosures hU hK
    (by exact_mod_cast hh.2.2.2.2.2.2.1) (by exact_mod_cast hh.2.2.2.2.2.2.2) hb

end LayerNode
end OptimalG.Certificates
