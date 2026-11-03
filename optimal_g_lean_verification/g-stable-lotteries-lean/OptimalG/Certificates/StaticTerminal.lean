import OptimalG.Certificates.StaticHighParameters
import OptimalG.Certificates.TensorBernstein
import OptimalG.VariationalDefs
namespace OptimalG.Certificates.StaticTerminal
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def parabola (z : ℝ) : ℝ := StaticHigh.contactValue+StaticHigh.contactScore*(z-StaticHigh.contact)-(189/200:ℝ)*(z-StaticHigh.contact)^2
noncomputable def A (x y : ℝ) : ℝ := (1/2)*x^1*y^1 + (-7298923/20000000)*x^1*y^0 + (11/200)*x^0*y^2 + (-87461887/250000000)*x^0*y^1 + (4521003582622389/20000000000000000)*x^0*y^0
noncomputable def B (x y : ℝ) : ℝ := (1/2)*x^0*y^2 + (-9169025015999574263180919081/12280038256362299233000000000)*x^0*y^1 + (8660255491894962963453/29222230000000000000000)*x^0*y^0
noncomputable def C (x y : ℝ) : ℝ := (-86242083/200000000)*x^0*y^1 + (308623637300048570530131021/1050573335467750000000000000)*x^0*y^0
def Alower : TensorBernstein3 := [⟨(53240613/2500000000), 0, 1, 0, 2, 0, 0⟩, ⟨(89493777/2500000000), 0, 1, 1, 1, 0, 0⟩, ⟨(9077041/625000000), 0, 1, 2, 0, 0, 0⟩, ⟨(85615613/2500000000), 1, 0, 0, 2, 0, 0⟩, ⟨(153368777/2500000000), 1, 0, 1, 1, 0, 0⟩, ⟨(16952041/625000000), 1, 0, 2, 0, 0, 0⟩]
theorem Alower_checked : Alower.check=true := by decide +kernel
theorem Alower_identity (u v : ℝ) : Alower.eval u v 0 =
    let x : ℝ := StaticHigh.contact-((21/25:ℝ)+(7/200)*u)
    let y : ℝ := (13/50:ℝ)+(1/50)*v-StaticHigh.contactRank
    A x y-1/5 := by
  norm_num [Alower,TensorBernstein3.eval,TensorBernsteinTerm3.eval,A,B,C,StaticHigh.contact,StaticHigh.contactRank] <;> ring
def Clower : TensorBernstein3 := [⟨(824703535220068025061752729/8404586683742000000000000000), 0, 0, 0, 1, 0, 0⟩, ⟨(752220628984070793603152729/8404586683742000000000000000), 0, 0, 1, 0, 0, 0⟩]
theorem Clower_checked : Clower.check=true := by decide +kernel
theorem Clower_identity (u v : ℝ) : Clower.eval u v 0 =
    let x : ℝ := StaticHigh.contact-((21/25:ℝ)+(7/200)*u)
    let y : ℝ := (13/50:ℝ)+(1/50)*v-StaticHigh.contactRank
    C x y-1/5 := by
  norm_num [Clower,TensorBernstein3.eval,TensorBernsteinTerm3.eval,A,B,C,StaticHigh.contact,StaticHigh.contactRank] <;> ring
def Blower : TensorBernstein3 := [⟨(20176207849390800399342014879629/66378585169525941800000000000000), 0, 0, 0, 2, 0, 0⟩, ⟨(727933394510092799825377924184273/1228003825636229923300000000000000), 0, 0, 1, 1, 0, 0⟩, ⟨(709838300122980476844421297822273/2456007651272459846600000000000000), 0, 0, 2, 0, 0, 0⟩]
theorem Blower_checked : Blower.check=true := by decide +kernel
theorem Blower_identity (u v : ℝ) : Blower.eval u v 0 =
    let x : ℝ := StaticHigh.contact-((21/25:ℝ)+(7/200)*u)
    let y : ℝ := (13/50:ℝ)+(1/50)*v-StaticHigh.contactRank
    B x y := by
  norm_num [Blower,TensorBernstein3.eval,TensorBernsteinTerm3.eval,A,B,C,StaticHigh.contact,StaticHigh.contactRank] <;> ring
def Bupper : TensorBernstein3 := [⟨(6375226218419576320657985120371/66378585169525941800000000000000), 0, 0, 0, 2, 0, 0⟩, ⟨(254469665998891138814622075815727/1228003825636229923300000000000000), 0, 0, 1, 1, 0, 0⟩, ⟨(272564760386003461795578702177727/2456007651272459846600000000000000), 0, 0, 2, 0, 0, 0⟩]
theorem Bupper_checked : Bupper.check=true := by decide +kernel
theorem Bupper_identity (u v : ℝ) : Bupper.eval u v 0 =
    let x : ℝ := StaticHigh.contact-((21/25:ℝ)+(7/200)*u)
    let y : ℝ := (13/50:ℝ)+(1/50)*v-StaticHigh.contactRank
    2/5-B x y := by
  norm_num [Bupper,TensorBernstein3.eval,TensorBernsteinTerm3.eval,A,B,C,StaticHigh.contact,StaticHigh.contactRank] <;> ring
theorem coefficient_bounds {z q : ℝ} (hz : z∈Icc (21/25:ℝ) (7/8))
    (hq : q∈Icc (13/50:ℝ) (7/25)) :
    (1/5:ℝ)≤A (StaticHigh.contact-z) (q-StaticHigh.contactRank) ∧
    (1/5:ℝ)≤C (StaticHigh.contact-z) (q-StaticHigh.contactRank) ∧
    (0:ℝ)≤B (StaticHigh.contact-z) (q-StaticHigh.contactRank) ∧
    B (StaticHigh.contact-z) (q-StaticHigh.contactRank)≤2/5 := by
  let u : ℝ := (z-21/25)/(7/200)
  let v : ℝ := (q-13/50)/(1/50)
  have hu : u∈Icc (0:ℝ) 1 := by
    have h := normalized_coordinate_mem (by norm_num : (21/25:ℝ)<7/8) hz
    norm_num at h
    exact h
  have hv : v∈Icc (0:ℝ) 1 := by
    have h := normalized_coordinate_mem (by norm_num : (13/50:ℝ)<7/25) hq
    norm_num at h
    exact h
  have hzu : (21/25:ℝ)+(7/200)*u=z := by dsimp [u]; ring
  have hqv : (13/50:ℝ)+(1/50)*v=q := by dsimp [v]; ring
  have hA := TensorBernstein3.check_sound Alower_checked hu hv (by norm_num : (0:ℝ)∈Icc 0 1)
  have hC := TensorBernstein3.check_sound Clower_checked hu hv (by norm_num : (0:ℝ)∈Icc 0 1)
  have hBl := TensorBernstein3.check_sound Blower_checked hu hv (by norm_num : (0:ℝ)∈Icc 0 1)
  have hBu := TensorBernstein3.check_sound Bupper_checked hu hv (by norm_num : (0:ℝ)∈Icc 0 1)
  rw [Alower_identity,hzu,hqv] at hA
  rw [Clower_identity,hzu,hqv] at hC
  rw [Blower_identity,hzu,hqv] at hBl
  rw [Bupper_identity,hzu,hqv] at hBu
  exact ⟨by linarith,by linarith,hBl,by linarith⟩

theorem cleared_identity (z q : ℝ) (hq : q≠1) (hL : (StaticLow.lam:ℝ)≠q) :
    (parabola z-Variational.terminalBound StaticLow.lam StaticLow.slack z q)*
      ((StaticLow.lam:ℝ)-q)*(1-q)=
      (StaticHigh.contact-z)^2*A (StaticHigh.contact-z) (q-StaticHigh.contactRank)+
      (StaticHigh.contact-z)*(q-StaticHigh.contactRank)*B (StaticHigh.contact-z) (q-StaticHigh.contactRank)+
      (q-StaticHigh.contactRank)^2*C (StaticHigh.contact-z) (q-StaticHigh.contactRank) := by
  unfold parabola Variational.terminalBound Variational.quadratic Variational.cap A B C
  field_simp [sub_ne_zero.mpr hq.symm,sub_ne_zero.mpr hL]
  norm_num [StaticLow.lam,StaticLow.slack,StaticHigh.contact,StaticHigh.contactRank,
    StaticHigh.contactValue,StaticHigh.contactScore] <;> ring

theorem terminal_le_parabola {z q : ℝ} (hz : z∈Icc (21/25:ℝ) (7/8))
    (hq : q∈Icc (13/50:ℝ) (7/25)) :
    Variational.terminalBound StaticLow.lam StaticLow.slack z q≤parabola z := by
  obtain ⟨ha,hc,hbl,hbu⟩ := coefficient_bounds hz hq
  let x : ℝ := StaticHigh.contact-z
  let y : ℝ := q-StaticHigh.contactRank
  have hax := mul_le_mul_of_nonneg_right ha (sq_nonneg x)
  have hcy := mul_le_mul_of_nonneg_right hc (sq_nonneg y)
  have hp : 0≤x^2*A x y+x*y*B x y+y^2*C x y := by
    change (1/5:ℝ)*x^2≤A x y*x^2 at hax
    change (1/5:ℝ)*y^2≤C x y*y^2 at hcy
    change 0≤B x y at hbl
    change B x y≤2/5 at hbu
    by_cases hxy : 0≤x*y
    · have hb := mul_nonneg hxy hbl
      nlinarith only [hax,hcy,hb,sq_nonneg x,sq_nonneg y]
    · have hb := mul_le_mul_of_nonpos_left hbu (le_of_not_ge hxy)
      nlinarith only [hax,hcy,hb,sq_nonneg (x+y)]
  have hLq : 0<(StaticLow.lam:ℝ)-q := by norm_num [StaticLow.lam]; linarith [hq.2]
  have h1q : 0<1-q := by linarith [hq.2]
  rw [←cleared_identity z q (by linarith) (by linarith)] at hp
  have hh := (mul_nonneg_iff_of_pos_right h1q).mp hp
  have hh' := (mul_nonneg_iff_of_pos_right hLq).mp hh
  linarith only [hh']
end OptimalG.Certificates.StaticTerminal
