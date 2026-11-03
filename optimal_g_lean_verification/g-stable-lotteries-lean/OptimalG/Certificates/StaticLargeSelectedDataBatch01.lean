import OptimalG.Certificates.ScaledTensorReconstruction
import OptimalG.Certificates.LargeSelectedExpressions
import OptimalG.Certificates.StaticLowParameters


namespace OptimalG.Certificates.StaticLargeSelectedData.HeadHeadDerivative
open Set LargeSelectedExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def numeratorPolynomial : RationalPolynomial3 := [[[(21287425753467417382430232813664705755779/50645759100327616479602220000000000000000)]], [[(-1407814513295044160849726535727346023/3165359943770476029975138750000000000)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-175335840815199903392673479275762381531/11254613133406136995467160000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(391/500), (7/8)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 33763839400218410986401480000000000000000
def numeratorCertificate : TensorBernstein3 := [
  ⟨1922559519634283517740949161268814399409, 0, 1, 0, 0, 0, 0⟩,
  ⟨526007522445599710178020437827287144593, 1, 0, 0, 0, 0, 0⟩]
noncomputable def numerator (x u v : ℝ) : ℝ := numeratorPolynomial.eval x u v

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {x u v : ℝ}
    (hx : x∈Icc (391/500) (7/8))
    (hu : u∈Icc 0 1)
    (hv : v∈Icc 0 1)
    : 0<numerator x u v := by
  have hx : ∀ i,(numeratorBox i).Contains (![x, u, v] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hx
    · simpa [numeratorBox,RatInterval.Contains] using hu
    · simpa [numeratorBox,RatInterval.Contains] using hv
  have hh := TensorBernstein3.scaledBoxCheck_sound numeratorChecked ![x, u, v] hx
  have he : numeratorReduced.eval x u v=numerator x u v-(175335840815199903392673479275762381531/11254613133406136995467160000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval x u v at hh
  rw [he] at hh
  have hm : (0:ℝ)<(175335840815199903392673479275762381531/11254613133406136995467160000000000000000) := by norm_num
  linarith only [hh,hm]

theorem expression_identity (x : ℝ) : numerator x 0 0=headHeadDerivative (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) x := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,
    RationalPolynomial.eval,headMassDerivative,middleMassDerivative,lateMassDerivative,
    massDerivativeBound,areaSlope,flat,cubic,primitiveCap,flatNumerator,atMass,
    headHeadDerivative,headFlatDerivative,capMaximum,kink,smallSplitK,
    SmallMassExpressions.initial,SmallMassExpressions.slope,SmallMassExpressions.primitive,
    headInitial,headSlope,Variational.capDeficit,Variational.capSlack,Variational.cap,
    Variational.capScore,Variational.quadratic,cubicControlDeficit,
    LineControl.slope,LineControl.alpha,LineControl.crossing,LineControl.denominator,
    LineControl.slopeNumerator,StaticLow.lam,StaticLow.slack]
  <;> ring

theorem positive {x : ℝ} (hx : x∈Icc (391/500:ℝ) (7/8)) : 0<(headHeadDerivative (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) x) := by
  rw [←expression_identity]
  exact numerator_pos hx (by norm_num) (by norm_num)

end OptimalG.Certificates.StaticLargeSelectedData.HeadHeadDerivative


namespace OptimalG.Certificates.StaticLargeSelectedData.HeadMassDerivative
open Set LargeSelectedExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def numeratorPolynomial : RationalPolynomial3 := [[[(2935092368647291258108985219/42022933418710000000000000000)]], [[(-2591363807897105893106749154731354687/2402550241951025449696500000000000000)]], [[(3/2)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-60358957420706837090321772073288573/48051004839020508993930000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(13/20), (7/8)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 96102009678041017987860000000000000000
def numeratorCertificate : TensorBernstein3 := [
  ⟨120717914841413674180643544146577146, 0, 2, 0, 0, 0, 0⟩,
  ⟨19083918304849370952574119695710962109, 1, 1, 0, 0, 0, 0⟩,
  ⟨26260946749934197081846594901564384963, 2, 0, 0, 0, 0, 0⟩]
noncomputable def numerator (x u v : ℝ) : ℝ := numeratorPolynomial.eval x u v

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {x u v : ℝ}
    (hx : x∈Icc (13/20) (7/8))
    (hu : u∈Icc 0 1)
    (hv : v∈Icc 0 1)
    : 0<numerator x u v := by
  have hx : ∀ i,(numeratorBox i).Contains (![x, u, v] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hx
    · simpa [numeratorBox,RatInterval.Contains] using hu
    · simpa [numeratorBox,RatInterval.Contains] using hv
  have hh := TensorBernstein3.scaledBoxCheck_sound numeratorChecked ![x, u, v] hx
  have he : numeratorReduced.eval x u v=numerator x u v-(60358957420706837090321772073288573/48051004839020508993930000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval x u v at hh
  rw [he] at hh
  have hm : (0:ℝ)<(60358957420706837090321772073288573/48051004839020508993930000000000000000) := by norm_num
  linarith only [hh,hm]

theorem expression_identity (x : ℝ) : numerator x 0 0=-(headMassDerivative (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) x) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,
    RationalPolynomial.eval,headMassDerivative,middleMassDerivative,lateMassDerivative,
    massDerivativeBound,areaSlope,flat,cubic,primitiveCap,flatNumerator,atMass,
    headHeadDerivative,headFlatDerivative,capMaximum,kink,smallSplitK,
    SmallMassExpressions.initial,SmallMassExpressions.slope,SmallMassExpressions.primitive,
    headInitial,headSlope,Variational.capDeficit,Variational.capSlack,Variational.cap,
    Variational.capScore,Variational.quadratic,cubicControlDeficit,
    LineControl.slope,LineControl.alpha,LineControl.crossing,LineControl.denominator,
    LineControl.slopeNumerator,StaticLow.lam,StaticLow.slack]
  <;> ring

theorem positive {x : ℝ} (hx : x∈Icc (13/20:ℝ) (7/8)) : 0<(-(headMassDerivative (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) x)) := by
  rw [←expression_identity]
  exact numerator_pos hx (by norm_num) (by norm_num)

end OptimalG.Certificates.StaticLargeSelectedData.HeadMassDerivative


namespace OptimalG.Certificates.StaticLargeSelectedData.LateMassDerivative
open Set LargeSelectedExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def numeratorPolynomial : RationalPolynomial3 := [[[(15633912151476202359220985219/84045866837420000000000000000)]], [[(-125267/100000)]], [[(3/2)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-464851852391034949220985219/168091733674840000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(13/20), (7/8)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 168091733674840000000000000000
def numeratorCertificate : TensorBernstein3 := [
  ⟨464851852391034949220985219, 0, 2, 0, 0, 0, 0⟩,
  ⟨27303170649564209768441970438, 1, 1, 0, 0, 0, 0⟩,
  ⟨39602784823106337319220985219, 2, 0, 0, 0, 0, 0⟩]
noncomputable def numerator (x u v : ℝ) : ℝ := numeratorPolynomial.eval x u v

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {x u v : ℝ}
    (hx : x∈Icc (13/20) (7/8))
    (hu : u∈Icc 0 1)
    (hv : v∈Icc 0 1)
    : 0<numerator x u v := by
  have hx : ∀ i,(numeratorBox i).Contains (![x, u, v] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hx
    · simpa [numeratorBox,RatInterval.Contains] using hu
    · simpa [numeratorBox,RatInterval.Contains] using hv
  have hh := TensorBernstein3.scaledBoxCheck_sound numeratorChecked ![x, u, v] hx
  have he : numeratorReduced.eval x u v=numerator x u v-(464851852391034949220985219/168091733674840000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval x u v at hh
  rw [he] at hh
  have hm : (0:ℝ)<(464851852391034949220985219/168091733674840000000000000000) := by norm_num
  linarith only [hh,hm]

theorem expression_identity (x : ℝ) : numerator x 0 0=-(lateMassDerivative (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) x) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,
    RationalPolynomial.eval,headMassDerivative,middleMassDerivative,lateMassDerivative,
    massDerivativeBound,areaSlope,flat,cubic,primitiveCap,flatNumerator,atMass,
    headHeadDerivative,headFlatDerivative,capMaximum,kink,smallSplitK,
    SmallMassExpressions.initial,SmallMassExpressions.slope,SmallMassExpressions.primitive,
    headInitial,headSlope,Variational.capDeficit,Variational.capSlack,Variational.cap,
    Variational.capScore,Variational.quadratic,cubicControlDeficit,
    LineControl.slope,LineControl.alpha,LineControl.crossing,LineControl.denominator,
    LineControl.slopeNumerator,StaticLow.lam,StaticLow.slack]
  <;> ring

theorem positive {x : ℝ} (hx : x∈Icc (13/20:ℝ) (7/8)) : 0<(-(lateMassDerivative (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) x)) := by
  rw [←expression_identity]
  exact numerator_pos hx (by norm_num) (by norm_num)

end OptimalG.Certificates.StaticLargeSelectedData.LateMassDerivative


namespace OptimalG.Certificates.StaticLargeSelectedData.MiddleMassDerivative
open Set LargeSelectedExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def numeratorPolynomial : RationalPolynomial3 := [[[(4203035840777998633158985219/42022933418710000000000000000)]], [[(-55017/50000)]], [[(3/2)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-779385432222276223158985219/84045866837420000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(13/20), (7/8)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 84045866837420000000000000000
def numeratorCertificate : TensorBernstein3 := [
  ⟨779385432222276223158985219, 0, 2, 0, 0, 0, 0⟩,
  ⟨17626113388288064816317970438, 1, 1, 0, 0, 0, 0⟩,
  ⟨23228960969032369843158985219, 2, 0, 0, 0, 0, 0⟩]
noncomputable def numerator (x u v : ℝ) : ℝ := numeratorPolynomial.eval x u v

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {x u v : ℝ}
    (hx : x∈Icc (13/20) (7/8))
    (hu : u∈Icc 0 1)
    (hv : v∈Icc 0 1)
    : 0<numerator x u v := by
  have hx : ∀ i,(numeratorBox i).Contains (![x, u, v] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hx
    · simpa [numeratorBox,RatInterval.Contains] using hu
    · simpa [numeratorBox,RatInterval.Contains] using hv
  have hh := TensorBernstein3.scaledBoxCheck_sound numeratorChecked ![x, u, v] hx
  have he : numeratorReduced.eval x u v=numerator x u v-(779385432222276223158985219/84045866837420000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval x u v at hh
  rw [he] at hh
  have hm : (0:ℝ)<(779385432222276223158985219/84045866837420000000000000000) := by norm_num
  linarith only [hh,hm]

theorem expression_identity (x : ℝ) : numerator x 0 0=-(middleMassDerivative (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) x) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,
    RationalPolynomial.eval,headMassDerivative,middleMassDerivative,lateMassDerivative,
    massDerivativeBound,areaSlope,flat,cubic,primitiveCap,flatNumerator,atMass,
    headHeadDerivative,headFlatDerivative,capMaximum,kink,smallSplitK,
    SmallMassExpressions.initial,SmallMassExpressions.slope,SmallMassExpressions.primitive,
    headInitial,headSlope,Variational.capDeficit,Variational.capSlack,Variational.cap,
    Variational.capScore,Variational.quadratic,cubicControlDeficit,
    LineControl.slope,LineControl.alpha,LineControl.crossing,LineControl.denominator,
    LineControl.slopeNumerator,StaticLow.lam,StaticLow.slack]
  <;> ring

theorem positive {x : ℝ} (hx : x∈Icc (13/20:ℝ) (7/8)) : 0<(-(middleMassDerivative (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) x)) := by
  rw [←expression_identity]
  exact numerator_pos hx (by norm_num) (by norm_num)

end OptimalG.Certificates.StaticLargeSelectedData.MiddleMassDerivative


namespace OptimalG.Certificates.StaticLargeSelectedData.SmallSplitK
open Set LargeSelectedExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def numeratorPolynomial : RationalPolynomial3 := [[[(8417469160054215861844091099233474387769593020466608713932032171851065619119836757251528258341227595098952957068362561270021452364728283180414878468942743612709598455744894136053609735791075256191015301/35578554154855958694189463558078015900482441431946473597418344126981485220872095665924832612264494261950220850747075616091286145019191959129275826967891881257844614559876474438547819224124000000000000000)]], [[(10838847937113318978132623330182098375249520466962606749307388283797941785605693939534783871929814160600625440279543088809242995123892418702529626430762442483099768715476959987395025335334705707540625161/40025873424212953530963146502837767888042746610939782797095637142854170873481107624165436688797556044693998457090460068102696913146590954020435305338878366415075191379861033743366296627139500000000000000)]], [[(-27162810868675894787302209981941006538596843489813130640234664191887393323419746770106416364241879948183672842899134200191047539276540392140842535617425697859503095297/23680854436488792996767772813314879120456798963191583286729292562009217560349770581991623885265365046453089394746163517900096431724000844647843925230608415375000000000)]], [[(550009458783099338143503552398552899494816844833760548113299663976358067299646039869567950000000000/531143734314741269574302952774985836867265472453402270056713381376409147215804877665613955976186323)]], [[(-259865975798194104548234442758592716210389327234449742582643980483006798460530000000000000000000000/531143734314741269574302952774985836867265472453402270056713381376409147215804877665613955976186323)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-10041966605845723693977292901181436331901225751619992148619822009662630823599355502844374019954877861374169113822236434165214296037698435127253625492563488890961142639849925437563042886979322254812213/8894638538713989673547365889519503975120610357986618399354586031745371305218023916481208153066123565487555212686768904022821536254797989782318956741972970314461153639969118609636954806031000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(391/500), (7/8)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 13341957808070984510321048834279255962680915536979927599031879047618056957827035874721812229599185348231332819030153356034232304382196984673478435112959455471691730459953677914455432209046500000000000000000
def numeratorCertificate : TensorBernstein3 := [
  ⟨774036584075978060857825113619684409614187212052512507612402424222899256576565181525824095324126808317805736222891918119882537298969611576633623518077649763351226319926689467925496685873485375474845615617, 0, 4, 0, 0, 0, 0⟩,
  ⟨2402153701967727687461824110620343451616251726599162929510567244104683366333551491612389974697281644144906456490419507973684437608370454872010312511950331205806959666542617710880080543735276637277759367243, 1, 3, 0, 0, 0, 0⟩,
  ⟨2503059783964748912732425709901730040678498749929729287501064367546179703263272124339788643389447446188857265287195757958182893161330815240546886176316629879302249747575787671347502230855566131513200207135, 2, 2, 0, 0, 0, 0⟩,
  ⟨890493918220741503826263773585933400683724210197780802012539424475934180959420628128710768293932935499149355446709046770036649209430747369967811345100568214292340869517704567164262937324243853092504775009, 3, 1, 0, 0, 0, 0⟩,
  ⟨15062949908768585540965939351772154497851838627429988222929733014493946235399033254266561029932316792061253670733354651247821444056547652690880438238845233336441713959774888156344564330468983382218319500, 4, 0, 0, 0, 0, 0⟩]
noncomputable def numerator (x u v : ℝ) : ℝ := numeratorPolynomial.eval x u v

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {x u v : ℝ}
    (hx : x∈Icc (391/500) (7/8))
    (hu : u∈Icc 0 1)
    (hv : v∈Icc 0 1)
    : 0<numerator x u v := by
  have hx : ∀ i,(numeratorBox i).Contains (![x, u, v] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hx
    · simpa [numeratorBox,RatInterval.Contains] using hu
    · simpa [numeratorBox,RatInterval.Contains] using hv
  have hh := TensorBernstein3.scaledBoxCheck_sound numeratorChecked ![x, u, v] hx
  have he : numeratorReduced.eval x u v=numerator x u v-(10041966605845723693977292901181436331901225751619992148619822009662630823599355502844374019954877861374169113822236434165214296037698435127253625492563488890961142639849925437563042886979322254812213/8894638538713989673547365889519503975120610357986618399354586031745371305218023916481208153066123565487555212686768904022821536254797989782318956741972970314461153639969118609636954806031000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval x u v at hh
  rw [he] at hh
  have hm : (0:ℝ)<(10041966605845723693977292901181436331901225751619992148619822009662630823599355502844374019954877861374169113822236434165214296037698435127253625492563488890961142639849925437563042886979322254812213/8894638538713989673547365889519503975120610357986618399354586031745371305218023916481208153066123565487555212686768904022821536254797989782318956741972970314461153639969118609636954806031000000000000000) := by norm_num
  linarith only [hh,hm]

theorem expression_identity (x : ℝ) : numerator x 0 0=-(smallSplitK (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) x) := by
  norm_num [numerator,numeratorPolynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,
    RationalPolynomial.eval,headMassDerivative,middleMassDerivative,lateMassDerivative,
    massDerivativeBound,areaSlope,flat,cubic,primitiveCap,flatNumerator,atMass,
    headHeadDerivative,headFlatDerivative,capMaximum,kink,smallSplitK,
    SmallMassExpressions.initial,SmallMassExpressions.slope,SmallMassExpressions.primitive,
    headInitial,headSlope,Variational.capDeficit,Variational.capSlack,Variational.cap,
    Variational.capScore,Variational.quadratic,cubicControlDeficit,
    LineControl.slope,LineControl.alpha,LineControl.crossing,LineControl.denominator,
    LineControl.slopeNumerator,StaticLow.lam,StaticLow.slack]
  <;> ring

theorem positive {x : ℝ} (hx : x∈Icc (391/500:ℝ) (7/8)) : 0<(-(smallSplitK (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) x)) := by
  rw [←expression_identity]
  exact numerator_pos hx (by norm_num) (by norm_num)

end OptimalG.Certificates.StaticLargeSelectedData.SmallSplitK
