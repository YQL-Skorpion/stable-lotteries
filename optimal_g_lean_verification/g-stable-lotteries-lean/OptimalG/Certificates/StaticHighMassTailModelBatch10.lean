import OptimalG.Certificates.ScaledTensorReconstruction5
import OptimalG.LargeTailLateHeadAssembly
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighForwardRight
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-14398190726384118151062388417618935424177/7397714972150420675719680000000000000000)], [(4920299823205495496593897496055987404819/924714371518802584464960000000000000000)], [(-13314244191605251104900688827108780701/3945447985146891027050496000000000000)]], [[(14235553745142617039661976450543749078424913/1323497444236286199015474000000000000000000)], [(-34289044531749067/1100249668800000)], [(118198340979913/4694398586880)], [(-43455625/10176896)]], [[(-1161603095317/176039947008)], [(374950125023/22004993376)], [(-671345950625/58679982336)]], [[(1/2)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := flatHigh (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (StaticLow.lam:ℝ) 0
theorem identity (p z : ℝ) (hs : Variational.capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000)≠0) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,highCapCleared,flatHigh,
    base,splitLinear,flat,massCap,massLower,kink,Variational.capDeficit,Variational.cap,
    Variational.quadratic,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  field_simp [hs]
  norm_num [Variational.capSlack,Variational.capScore]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighForwardRight


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighForwardKink
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-682135373961459664533260718447260846677428971104421977650425537656295266342937/22603864743850671720679220480000000000000000000000)], [(72160443623249265892913455269153796528705074364653256047636571989199184123/904154589754026868827168819200000000000000000)], [(-585794647824073463078033116602309297272133898992822591809772026820437151/11573178748851543920987760885760000000000000)]], [[(936549731831415837215228630732924615924011239348968145561322850613058867349/5650966185962667930169805120000000000000000000)], [(-506899046362289802875186547839781998957718124819747/1075787095518976000000)], [(5200442062747676760156250282651960839795009173763/13770074822642892800)], [(-1102426184842088323100531338618676215185907125/17212593528303616)]], [[(-53022341284790066218244856255475787630068578096773/537893547759488000000)], [(5498967203308667631135818983604593324053042791/21515741910379520)], [(-5907520683186063997079468834658317325149871375/34425187056607232)]], [[(10085069387247326014152822004004670263146131/1344733869398720)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[(10085069387247326014152822004004670263146131/672366934699360)]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := flatHigh (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) (kink (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) 0
theorem identity (p z : ℝ) (hs : Variational.capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000)≠0) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,highCapCleared,flatHigh,
    base,splitLinear,flat,massCap,massLower,kink,Variational.capDeficit,Variational.cap,
    Variational.quadratic,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  field_simp [hs]
  norm_num [Variational.capSlack,Variational.capScore]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighForwardKink


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighCapMax
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-36669169118411391045002786505191449837422018324567700532828675161/528402076731425941265757795165536400000000000000000000000000000000)]], [[(-35042990342848522461373323593071938698363800575790803515874435282910813789/14066963816967070501821515770668301730852415000000000000000000000000000000)], [(73750053887158160962879085854928709925157/9247143715188025844649600000000000000000)], [(-36237363230979920656676949928455526953/6575746641911485045084160000000000000)]], [[(5474546541529662666925469684896172559781648415272624209727464317443246421696475673/349471167392896459252094664523549363748768780796375750000000000000000000000000000)], [(-918223107951025946636930044037153912053681/19351654982649691481371269250000000000000)], [(311102219493989/7823997644800)], [(-70963875/10176896)]], [[(-3463013158267425651300936030670032885222118831/334744927889874363244760215486500000000000000)], [(5993944426649/220049933760)], [(-365440301625/19559994112)]], [[(1329399613/1496104020)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := highCapCleared (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000)
theorem identity (p z : ℝ) (hs : Variational.capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000)≠0) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,highCapCleared,flatHigh,
    base,splitLinear,flat,massCap,massLower,kink,Variational.capDeficit,Variational.cap,
    Variational.quadratic,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  field_simp [hs]
  norm_num [Variational.capSlack,Variational.capScore]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighCapMax


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighForwardLeft
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-4452077509332428265780413990893439031558219/2568651031996673845736000000000000000000000)], [(8735782020390606888986639406597660092413/1849428743037605168929920000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(7391108894632577821656280655006861847347269163/781084075006781571785632239000000000000000000)], [(-60924234795087137/2200499337600000)], [(106308739046263/4694398586880)], [(-39424375/10176896)]], [[(-342644196987551/61124981600000)], [(660766858321/44009986752)], [(-609067169375/58679982336)]], [[(1/2)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := flatHigh (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) (1459/5000) (Variational.capDeficit (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000))
theorem identity (p z : ℝ) (hs : Variational.capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000)≠0) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,highCapCleared,flatHigh,
    base,splitLinear,flat,massCap,massLower,kink,Variational.capDeficit,Variational.cap,
    Variational.quadratic,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  field_simp [hs]
  norm_num [Variational.capSlack,Variational.capScore]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighForwardLeft


namespace OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighForwardRight
open Set LargeTailExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def numeratorPolynomial : RationalPolynomial3 := [[[(-12294776062199977145523463921105936024027/7397714972150420675719680000000000000000)], [(8735782020390606888986639406597660092413/1849428743037605168929920000000000000000)], [(-12079121076993306885558983309485175651/3945447985146891027050496000000000000)]], [[(12101861418776144863888859550067186578424913/1323497444236286199015474000000000000000000)], [(-60328933709286209/2200499337600000)], [(106308739046263/4694398586880)], [(-39424375/10176896)]], [[(-991905872167/176039947008)], [(660766858321/44009986752)], [(-609067169375/58679982336)]], [[(1/2)]]]
noncomputable def numerator (p z dummy : ℝ) : ℝ := numeratorPolynomial.eval p z dummy
def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
noncomputable def denominator (p z dummy : ℝ) : ℝ := denominatorPolynomial.eval p z dummy
noncomputable def target (p z : ℝ) : ℝ := flatHigh (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) (StaticLow.lam:ℝ) 0
theorem identity (p z : ℝ) (hs : Variational.capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000)≠0) :
    numerator p z 0= -target p z * denominator p z 0 := by
  norm_num [StaticLow.lam,StaticLow.slack,numerator,numeratorPolynomial,denominator,denominatorPolynomial,
    RationalPolynomial5.eval,RationalPolynomial4.eval,RationalPolynomial3.eval,
    RationalPolynomial2.eval,RationalPolynomial.eval,target,highCapCleared,flatHigh,
    base,splitLinear,flat,massCap,massLower,kink,Variational.capDeficit,Variational.cap,
    Variational.quadratic,tailScore,tailPrimitive,tailOne,tailTwo,tailCoord]
  field_simp [hs]
  norm_num [Variational.capSlack,Variational.capScore]
  <;> ring

end OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighForwardRight
