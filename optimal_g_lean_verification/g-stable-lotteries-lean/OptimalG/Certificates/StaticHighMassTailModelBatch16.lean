import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower1Head
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-41845753856088179945634469864464173007191731/23117859287970064611624000000000000000000000), (191491955753789801448326436840869/726912702276845580000000000000000)], [(2749527863584958928395524175384212333919/616476247679201722976640000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(193986576627636264170892699541767823861/19264882739975053843020000000000000000), (-1018119217/864900000)], [(-157967429434140856981725611905127785763671421/5921606424690805593299608390500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(4389849557964677776253977962908294029503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-40718998488178813737932119250927115955078579/5921606424690805593299608390500000000000000), (11019051113621970269613616872375743/52755999062841267166252312500000000)], [(198882773394973222243100582260928401341397/12583413652467961885761667829812500000000)], [(-609067169375/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3514/10000) (p-z+r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
theorem identity (p z r : ℝ) :
    numerator p z r= -target p z r * denominator p z r := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,core,massCap,massLower,
    SmallMassExpressions.primitive,SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic,
    lateHeadCone,lateHeadNearLine,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring
theorem nonpos {p z r : ℝ}
    (hn : 0≤numerator p z r) (hd : 0<denominator p z r) :
    target p z r≤0 := by
  rw [identity p z r] at hn
  have hh := (nonneg_of_mul_nonneg_left hn hd)
  linarith only [hh]

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower1Head


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower1Cap
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-2915494477574702813237842548895122427603822223649979/210114667093550000000000000000), (3339798080746431673307476472916619312436683602449979/210114667093550000000000000000), (-1060759007929322150174084810053742212082153447/525286667733875000000000)], [(574698689605762394122124022350269721614947422613/16809173367484000000000000), (-574698689605762394122124022350269721614947422613/16809173367484000000000000)], [(-2524744392110394502779545036287874212179939777/107578709551897600000000), (2524744392110394502779545036287874212179939777/107578709551897600000000)]], [[(4045756228675251039815991156638982644638481079485151/52528666773387500000000000000), (-44515591842464141491815932357736640855598087167/525286667733875000000000), (68314439031198640841871219602319756495747843/13132166693346875000000), (8610085269888390468975323667390315403897/3283041673336718750)], [(-2685446300380394568689335402387172357982414157/13132166693346875000000), (2754326982539501692441137991726294881213590157/13132166693346875000000), (-8610085269888390468975323667390315403897/1641520836668359375)], [(4389849557964677776253977962908294029503199/26264333386693750000), (-4389849557964677776253977962908294029503199/26264333386693750000)], [-29696246140119405468750, 29696246140119405468750]], [[(-692222974299039833544846027265760971236335843/13132166693346875000000), (713249175024417641310274103345888448005159843/13132166693346875000000), (-2628275090672225970678509510015934596103/1641520836668359375)], [(198882773394973222243100582260928401341397/1641520836668359375), (-198882773394973222243100582260928401341397/1641520836668359375)], [-79565956749688639453125, 79565956749688639453125]], [[(13866635451232842410332342687422184596103/3283041673336718750), (-13866635451232842410332342687422184596103/3283041673336718750)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[7665704492674813920000, -7665704492674813920000]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3514/10000) (p-z+r) (Variational.cap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
theorem identity (p z r : ℝ) (hr : r≠1) :
    numerator p z r= -target p z r * denominator p z r := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,core,massCap,massLower,
    SmallMassExpressions.primitive,SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic,
    lateHeadCone,lateHeadNearLine,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  have hd : (1:ℝ)-r≠0 := sub_ne_zero.mpr (Ne.symm hr)
  field_simp [hd]
  <;> ring
theorem nonpos {p z r : ℝ} (hr : r≠1)
    (hn : 0≤numerator p z r) (hd : 0<denominator p z r) :
    target p z r≤0 := by
  rw [identity p z r hr] at hn
  have hh := (nonneg_of_mul_nonneg_left hn hd)
  linarith only [hh]

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower1Cap


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower1Cone
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-41845753856088179945634469864464173007191731/23117859287970064611624000000000000000000000), (191491955753789801448326436840869/726912702276845580000000000000000)], [(2749527863584958928395524175384212333919/616476247679201722976640000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(97032067593736339735661836457665073861/9632441369987526921510000000000000000), (-88891599231139411059087132946671995297/74479057500481788940591500000000000000), (1069761957651165231815925679627229/316535994377047602997513875000000000)], [(-157967429434140856981725611905127785763671421/5921606424690805593299608390500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(4389849557964677776253977962908294029503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-40718998488178813737932119250927115955078579/5921606424690805593299608390500000000000000), (11019051113621970269613616872375743/52755999062841267166252312500000000)], [(198882773394973222243100582260928401341397/12583413652467961885761667829812500000000)], [(-609067169375/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3514/10000) (p-z+r) (lateHeadCone (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
theorem identity (p z r : ℝ) :
    numerator p z r= -target p z r * denominator p z r := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,core,massCap,massLower,
    SmallMassExpressions.primitive,SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic,
    lateHeadCone,lateHeadNearLine,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring
theorem nonpos {p z r : ℝ}
    (hn : 0≤numerator p z r) (hd : 0<denominator p z r) :
    target p z r≤0 := by
  rw [identity p z r] at hn
  have hh := (nonneg_of_mul_nonneg_left hn hd)
  linarith only [hh]

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower1Cone


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower1NearLine
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-41845753856088179945634469864464173007191731/23117859287970064611624000000000000000000000), (191491955753789801448326436840869/726912702276845580000000000000000)], [(2749527863584958928395524175384212333919/616476247679201722976640000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(97215182712290145119321471935165073861/9632441369987526921510000000000000000), (-96964384273616632162357845631671995297/74479057500481788940591500000000000000), (49974573088905019894931819367127229/316535994377047602997513875000000000)], [(-157967429434140856981725611905127785763671421/5921606424690805593299608390500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(4389849557964677776253977962908294029503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-40718998488178813737932119250927115955078579/5921606424690805593299608390500000000000000), (11019051113621970269613616872375743/52755999062841267166252312500000000)], [(198882773394973222243100582260928401341397/12583413652467961885761667829812500000000)], [(-609067169375/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3514/10000) (p-z+r) (lateHeadNearLine (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
theorem identity (p z r : ℝ) :
    numerator p z r= -target p z r * denominator p z r := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,core,massCap,massLower,
    SmallMassExpressions.primitive,SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic,
    lateHeadCone,lateHeadNearLine,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring
theorem nonpos {p z r : ℝ}
    (hn : 0≤numerator p z r) (hd : 0<denominator p z r) :
    target p z r≤0 := by
  rw [identity p z r] at hn
  have hh := (nonneg_of_mul_nonneg_left hn hd)
  linarith only [hh]

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower1NearLine


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower1Line
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-41845753856088179945634469864464173007191731/23117859287970064611624000000000000000000000), (191491955753789801448326436840869/726912702276845580000000000000000)], [(2749527863584958928395524175384212333919/616476247679201722976640000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(97215183550312544308236314106535073861/9632441369987526921510000000000000000), (-96964384273616632162357845631671995297/74479057500481788940591500000000000000), (49974573088905019894931819367127229/316535994377047602997513875000000000)], [(-157967429434140856981725611905127785763671421/5921606424690805593299608390500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(4389849557964677776253977962908294029503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-40718998488178813737932119250927115955078579/5921606424690805593299608390500000000000000), (11019051113621970269613616872375743/52755999062841267166252312500000000)], [(198882773394973222243100582260928401341397/12583413652467961885761667829812500000000)], [(-609067169375/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3514/10000) (p-z+r) (Variational.quadratic (StaticLow.lam:ℝ) r-(StaticLow.slack:ℝ)) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
theorem identity (p z r : ℝ) :
    numerator p z r= -target p z r * denominator p z r := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,core,massCap,massLower,
    SmallMassExpressions.primitive,SmallMassExpressions.initial,SmallMassExpressions.slope,
    headInitial,headSlope,Variational.cap,Variational.capScore,Variational.quadratic,
    lateHeadCone,lateHeadNearLine,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  <;> ring
theorem nonpos {p z r : ℝ}
    (hn : 0≤numerator p z r) (hd : 0<denominator p z r) :
    target p z r≤0 := by
  rw [identity p z r] at hn
  have hh := (nonneg_of_mul_nonneg_left hn hd)
  linarith only [hh]

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower1Line
