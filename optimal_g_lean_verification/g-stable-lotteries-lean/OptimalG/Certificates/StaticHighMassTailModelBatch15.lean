import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower0Head
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-48418924681663620587943608916067296132660481/23117859287970064611624000000000000000000000), (191491955753789801448326436840869/726912702276845580000000000000000)], [(1558900202795876814897954685277825286497/308238123839600861488320000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(225044689092941536016207356026142823861/19264882739975053843020000000000000000), (-1018119217/864900000)], [(-180166141566929227786138259439276453732421421/5921606424690805593299608390500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(4899773976270149873973548845065376549034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-46427249279753769734634573051806022205078579/5921606424690805593299608390500000000000000), (11019051113621970269613616872375743/52755999062841267166252312500000000)], [(224367951217076736149106414240689143528897/12583413652467961885761667829812500000000)], [(-671345950625/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (p-z+r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower0Head


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower0Cap
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-3373463123761062574024027589336287327678839290368729/210114667093550000000000000000), (3797766726932791434093661513357784212511700669168729/210114667093550000000000000000), (-1060759007929322150174084810053742212082153447/525286667733875000000000)], [(325836997558131818883562776288428765974083483819/8404586683742000000000000), (-325836997558131818883562776288428765974083483819/8404586683742000000000000)], [(-2782906400530186264585028089032159769474136127/107578709551897600000000), (2782906400530186264585028089032159769474136127/107578709551897600000000)]], [[(4694924283010475202774875400721145777450981079485151/52528666773387500000000000000), (-51007272385816383121404774798558272183723087167/525286667733875000000000), (68314439031198640841871219602319756495747843/13132166693346875000000), (8610085269888390468975323667390315403897/3283041673336718750)], [(-3062824406637796872364350410467699713451164157/13132166693346875000000), (3131705088796903996116152999806822236682340157/13132166693346875000000), (-8610085269888390468975323667390315403897/1641520836668359375)], [(4899773976270149873973548845065376549034449/26264333386693750000), (-4899773976270149873973548845065376549034449/26264333386693750000)], [-32732768399568194531250, 32732768399568194531250]], [[(-789263237755814085488787741880702377486335843/13132166693346875000000), (810289438481191893254215817960829854255159843/13132166693346875000000), (-2628275090672225970678509510015934596103/1641520836668359375)], [(224367951217076736149106414240689143528897/1641520836668359375), (-224367951217076736149106414240689143528897/1641520836668359375)], [-87701793098322760546875, 87701793098322760546875]], [[(13866635451232842410332342687422184596103/3283041673336718750), (-13866635451232842410332342687422184596103/3283041673336718750)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[7665704492674813920000, -7665704492674813920000]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (p-z+r) (Variational.cap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower0Cap


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower0Cone
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-48418924681663620587943608916067296132660481/23117859287970064611624000000000000000000000), (191491955753789801448326436840869/726912702276845580000000000000000)], [(1558900202795876814897954685277825286497/308238123839600861488320000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(112561123826388975658319164699852573861/9632441369987526921510000000000000000), (-88891599231139411059087132946671995297/74479057500481788940591500000000000000), (1069761957651165231815925679627229/316535994377047602997513875000000000)], [(-180166141566929227786138259439276453732421421/5921606424690805593299608390500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(4899773976270149873973548845065376549034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-46427249279753769734634573051806022205078579/5921606424690805593299608390500000000000000), (11019051113621970269613616872375743/52755999062841267166252312500000000)], [(224367951217076736149106414240689143528897/12583413652467961885761667829812500000000)], [(-671345950625/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (p-z+r) (lateHeadCone (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower0Cone


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower0NearLine
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-48418924681663620587943608916067296132660481/23117859287970064611624000000000000000000000), (191491955753789801448326436840869/726912702276845580000000000000000)], [(1558900202795876814897954685277825286497/308238123839600861488320000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(112744238944942781041978800177352573861/9632441369987526921510000000000000000), (-96964384273616632162357845631671995297/74479057500481788940591500000000000000), (49974573088905019894931819367127229/316535994377047602997513875000000000)], [(-180166141566929227786138259439276453732421421/5921606424690805593299608390500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(4899773976270149873973548845065376549034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-46427249279753769734634573051806022205078579/5921606424690805593299608390500000000000000), (11019051113621970269613616872375743/52755999062841267166252312500000000)], [(224367951217076736149106414240689143528897/12583413652467961885761667829812500000000)], [(-671345950625/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (p-z+r) (lateHeadNearLine (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower0NearLine


namespace OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower0Line
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-48418924681663620587943608916067296132660481/23117859287970064611624000000000000000000000), (191491955753789801448326436840869/726912702276845580000000000000000)], [(1558900202795876814897954685277825286497/308238123839600861488320000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(112744239782965180230893642348722573861/9632441369987526921510000000000000000), (-96964384273616632162357845631671995297/74479057500481788940591500000000000000), (49974573088905019894931819367127229/316535994377047602997513875000000000)], [(-180166141566929227786138259439276453732421421/5921606424690805593299608390500000000000000), (108293424099618781603825118132872771/158267997188523801498756937500000000)], [(4899773976270149873973548845065376549034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-46427249279753769734634573051806022205078579/5921606424690805593299608390500000000000000), (11019051113621970269613616872375743/52755999062841267166252312500000000)], [(224367951217076736149106414240689143528897/12583413652467961885761667829812500000000)], [(-671345950625/58679982336)]], [[(174407730781350603221506819367127229/316535994377047602997513875000000000)]]]
noncomputable def numerator (p z r : ℝ) : ℝ := numeratorPolynomial.eval p z r
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z r : ℝ) : ℝ := denominatorPolynomial.eval p z r
noncomputable def target (p z r : ℝ) : ℝ := core (StaticLow.lam:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (p-z+r) (Variational.quadratic (StaticLow.lam:ℝ) r-(StaticLow.slack:ℝ)) (SmallMassExpressions.primitive (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (p-z+r))
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

end OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedLower0Line
