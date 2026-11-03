import OptimalG.Certificates.StaticCompletion
import OptimalG.Certificates.StaticHighParameters
import OptimalG.HeadStationaryCurve

/-! Exact entry and terminal tangency algebra for the frozen static candidate. -/
namespace OptimalG.Certificates.StaticContact
open Set

noncomputable def initial : ℝ :=
  headInitial 0.2635 (cap StaticLow.lam StaticLow.slack 0.2635)
    (capSlope StaticLow.lam StaticLow.slack 0.2635)
noncomputable def level : ℝ :=
  headStationaryLevel StaticLow.lam StaticLow.slack initial StaticLow.affineHeadSlope 0.2635
noncomputable def entry : ℝ := 1-Real.sqrt level

theorem level_bounds : (0.15:ℝ)^2<level ∧ level<(0.151:ℝ)^2 := by
  norm_num [level,headStationaryLevel,headStationaryConstant,initial,
    StaticLow.affineHeadSlope,headSlope,headInitial,cap,capSlope,
    StaticLow.lam,StaticLow.slack]

theorem entry_mem : entry∈Ioo (0.849:ℝ) 0.85 := by
  have hn : 0≤level := by linarith only [level_bounds.1]
  have hs := Real.sq_sqrt hn
  have h0 := Real.sqrt_nonneg level
  have hl : (0.15:ℝ)<Real.sqrt level := by nlinarith only [hs,h0,level_bounds.1]
  have hu : Real.sqrt level<(0.151:ℝ) := by nlinarith only [hs,h0,level_bounds.2]
  unfold entry
  constructor <;> linarith only [hl,hu]

theorem entry_le_contact : entry≤(StaticHigh.contact:ℝ) := by
  have hc := (Rat.cast_lt (K:=ℝ)).mpr StaticHigh.parameter_bounds.1
  norm_num only [Rat.cast_ofScientific] at hc
  linarith only [entry_mem.2,hc]

theorem entry_identity :
    headStationaryLevel StaticLow.lam StaticLow.slack initial StaticLow.affineHeadSlope 0.2635=
      (1-entry)^2 := by
  have hn : 0≤level := by linarith only [level_bounds.1]
  change level=(1-(1-Real.sqrt level))^2
  convert! (Real.sq_sqrt hn).symm using 1 <;> ring

theorem contact_stationary :
    Variational.stationaryLevel StaticLow.lam StaticLow.slack StaticHigh.contactRank=
      (1-(StaticHigh.contact:ℝ))^2 := by
  norm_num [Variational.stationaryLevel,Variational.capSlack,Variational.capDeficit,
    Variational.capScore,Variational.cap,Variational.quadratic,
    StaticLow.lam,StaticLow.slack,StaticHigh.contactRank,StaticHigh.contact]

theorem contact_terminal : (StaticHigh.contactValue:ℝ)=
    Variational.terminalBound StaticLow.lam StaticLow.slack StaticHigh.contact StaticHigh.contactRank := by
  norm_num [Variational.terminalBound,Variational.cap,Variational.quadratic,
    StaticLow.lam,StaticLow.slack,StaticHigh.contactRank,StaticHigh.contact,StaticHigh.contactValue]

theorem contact_value : (StaticHigh.contactValue:ℝ)=StaticHigh.contact*
    ((1-(StaticHigh.contact:ℝ))-Variational.capSlack StaticLow.lam StaticLow.slack StaticHigh.contactRank) := by
  norm_num [Variational.capSlack,Variational.capScore,StaticLow.lam,StaticLow.slack,
    StaticHigh.contactRank,StaticHigh.contact,StaticHigh.contactValue]

theorem contact_score : (StaticHigh.contactScore:ℝ)=1-2*StaticHigh.contact-
    Variational.capSlack StaticLow.lam StaticLow.slack StaticHigh.contactRank+
      StaticHigh.contact*(1-(StaticHigh.contact:ℝ))/((StaticLow.lam:ℝ)-StaticHigh.contactRank) := by
  norm_num [Variational.capSlack,Variational.capScore,StaticLow.lam,StaticLow.slack,
    StaticHigh.contactRank,StaticHigh.contact,StaticHigh.contactScore]

theorem contact_time_derivative :
    HasDerivAt (fun z => Variational.terminalBound StaticLow.lam StaticLow.slack z StaticHigh.contactRank)
      (StaticHigh.contactScore:ℝ) StaticHigh.contact := by
  have hh := Variational.terminalBound_z_hasDerivAt (StaticLow.lam:ℝ) StaticLow.slack
    StaticHigh.contact StaticHigh.contactRank (by norm_num [StaticLow.lam,StaticHigh.contactRank])
  convert! hh using 1
  norm_num [Variational.capDeficit,Variational.cap,Variational.quadratic,
    StaticLow.lam,StaticLow.slack,StaticHigh.contactRank,StaticHigh.contact,StaticHigh.contactScore]

theorem contact_rank_derivative :
    HasDerivAt (Variational.terminalBound StaticLow.lam StaticLow.slack StaticHigh.contact) 0
      StaticHigh.contactRank := by
  have hh := Variational.terminalBound_q_hasDerivAt (StaticLow.lam:ℝ) StaticLow.slack
    StaticHigh.contact StaticHigh.contactRank (by norm_num [StaticLow.lam,StaticHigh.contactRank])
    (by norm_num [StaticHigh.contactRank])
  convert! hh using 1
  norm_num [Variational.capSlack,Variational.capDeficit,Variational.capScore,
    Variational.cap,Variational.quadratic,StaticLow.lam,StaticLow.slack,
    StaticHigh.contactRank,StaticHigh.contact]

end OptimalG.Certificates.StaticContact
