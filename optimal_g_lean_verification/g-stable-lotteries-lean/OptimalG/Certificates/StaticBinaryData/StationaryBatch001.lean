import OptimalG.Certificates.DenseBernstein


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadZeroLeaf002
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(-180317491532193675966270315016171491790320348145590768208350732820380768659537413/320379433449258456533627547002397782110866846662093757602156310000000000000000000)], [(-4082621980925186873086783342545737343387410002345119541765906696158980344739029/21104995178469900824152714658782953896553353523865426282042046921250000000000000)], [(8508121093812990732092247315434043610021/23172903769156025510721396258225000000000)]], [[(485206/366039)]], [[(-9866289593846817069548847529597155062485/13334973306909483549679633690867376738334)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-58332235841779643564077680916109998721348787313826798603635927287861949073/435002625185686974247966798373927742173614184198362196336940000000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(13/16), (17/20)⟩, ⟨0, (527/2000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 640758866898516913067255094004795564221733693324187515204312620000000000000000000
def numeratorCertificate : DenseBernstein3 := [[[16416411307095688907317019794172379401666186773093745041406782505530942029940645], [171846766789882829939772847978860056233093527426533748686311441790041301969058], [90056679367375715607609990117032949354310015472728626502100801343596423798613]], [[35794379081984103957845739070628581419181783975861934847598098714186884059881290], [6266806469165217946302944660525365344165007914201957026941690289830082603938116], [3141669826527477574426919462517888514558030460619902017788735305812192847597226]], [[18711285562208102567128206512619705514082892863202419343266090513343442029940645], [4761595277014710149562146284873512281066505707643882352404927457415041301969058], [2384930934479789375418796708564359061771016105581402928361408809156096423798613]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {p r u : ℝ}
    (hp : p∈Icc (13/16) (17/20))
    (hr : r∈Icc 0 (527/2000))
    (hu : u∈Icc 0 1)
    : 0<numerator p r u := by
  have hx : ∀ i,(numeratorBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hp
    · simpa [numeratorBox,RatInterval.Contains] using hr
    · simpa [numeratorBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![p, r, u] hx
  have he : numeratorReduced.eval p r u=numerator p r u-(58332235841779643564077680916109998721348787313826798603635927287861949073/435002625185686974247966798373927742173614184198362196336940000000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(58332235841779643564077680916109998721348787313826798603635927287861949073/435002625185686974247966798373927742173614184198362196336940000000000000000000) := by norm_num
  linarith only [hh,hm]

def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
def denominatorReduced : RationalPolynomial3 := denominatorPolynomial.add [[[(-1/2)]]]
def denominatorBox : Fin 3→RatInterval := ![⟨(13/16), (17/20)⟩, ⟨0, (527/2000)⟩, ⟨0, 1⟩]
def denominatorScale : ℚ := 2
def denominatorCertificate : DenseBernstein3 := [[[1]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u

theorem denominatorChecked : denominatorCertificate.scaledBoxCheck denominatorScale denominatorReduced denominatorBox=true := by
  decide +kernel

theorem denominator_pos {p r u : ℝ}
    (hp : p∈Icc (13/16) (17/20))
    (hr : r∈Icc 0 (527/2000))
    (hu : u∈Icc 0 1)
    : 0<denominator p r u := by
  have hx : ∀ i,(denominatorBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [denominatorBox,RatInterval.Contains] using hp
    · simpa [denominatorBox,RatInterval.Contains] using hr
    · simpa [denominatorBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound denominatorChecked ![p, r, u] hx
  have he : denominatorReduced.eval p r u=denominator p r u-(1/2) := by
    norm_num [denominatorReduced,RationalPolynomial3.eval_add,denominator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤denominatorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadZeroLeaf002


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf000
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(-108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(-2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[2]], [[-1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-68959115085732869865612338626827152983/60063756048775636242412500000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(31/40), (1557/2000)⟩, ⟨0, (527/4000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 120127512097551272484825000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[5099943566741934070118899954035084000605], [4579446796467076172734397911126837064496], [137918230171465739731224677253654305966]], [[10389087965037511394401399283070168001210], [9537295256041438853795994572253674128992], [465037291896574733626048729507308611932]], [[5287672836272382321194560222785084000605], [4954905335527972674885718448626837064496], [325647499701913990806884946003654305966]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (31/40) (1557/2000))
    (hr : r∈Icc 0 (527/4000))
    (hu : u∈Icc 0 1)
    : 0<exclusion p r u := by
  have hx : ∀ i,(exclusionBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [exclusionBox,RatInterval.Contains] using hp
    · simpa [exclusionBox,RatInterval.Contains] using hr
    · simpa [exclusionBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound exclusionChecked ![p, r, u] hx
  have he : exclusionReduced.eval p r u=exclusion p r u-(68959115085732869865612338626827152983/60063756048775636242412500000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(68959115085732869865612338626827152983/60063756048775636242412500000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf000


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf001
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(103613480548895019252353340621571692418431507853/58212771278620517460330073987500000000000000000)], [(2745323754157031595298922967313959297696231799/3834766307979126587699243623926562500000000000)], [(-48820510272562936270498158862482159900703/76695326159582531753984872478531250000000)]], [[(-602530742608298834135932781682649607821031/129361713952490038800733497750000000000000)], [(-49974573088905019894931819367127229/79133998594261900749378468750000000)]], [[(2922997/969183)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-35750241744631409815414618191173451557220077/232851085114482069841320295950000000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(31/40), (3107/4000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 232851085114482069841320295950000000000000000000
def numeratorCertificate : DenseBernstein3 := [[[60582510618795272106021641110462419622202627], [1022270612647893929943877828521929479756699350], [318477879188081972474042944398264603442734698]], [[94182066673870219700917887425920246179422704], [1973623238833838729001614470532458109169066150], [593020726477935138573070097080132949606119396]], [[35750241744631409815414618191173451557220077], [955653997565057723498773385761959879412366800], [276693532979409628319545524557583971163384698]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {p r u : ℝ}
    (hp : p∈Icc (31/40) (3107/4000))
    (hr : r∈Icc (527/4000) (1581/8000))
    (hu : u∈Icc 0 1)
    : 0<numerator p r u := by
  have hx : ∀ i,(numeratorBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hp
    · simpa [numeratorBox,RatInterval.Contains] using hr
    · simpa [numeratorBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![p, r, u] hx
  have he : numeratorReduced.eval p r u=numerator p r u-(35750241744631409815414618191173451557220077/232851085114482069841320295950000000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(35750241744631409815414618191173451557220077/232851085114482069841320295950000000000000000000) := by norm_num
  linarith only [hh,hm]

def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
def denominatorReduced : RationalPolynomial3 := denominatorPolynomial.add [[[(-1/2)]]]
def denominatorBox : Fin 3→RatInterval := ![⟨(31/40), (3107/4000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def denominatorScale : ℚ := 2
def denominatorCertificate : DenseBernstein3 := [[[1]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u

theorem denominatorChecked : denominatorCertificate.scaledBoxCheck denominatorScale denominatorReduced denominatorBox=true := by
  decide +kernel

theorem denominator_pos {p r u : ℝ}
    (hp : p∈Icc (31/40) (3107/4000))
    (hr : r∈Icc (527/4000) (1581/8000))
    (hu : u∈Icc 0 1)
    : 0<denominator p r u := by
  have hx : ∀ i,(denominatorBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [denominatorBox,RatInterval.Contains] using hp
    · simpa [denominatorBox,RatInterval.Contains] using hr
    · simpa [denominatorBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound denominatorChecked ![p, r, u] hx
  have he : denominatorReduced.eval p r u=denominator p r u-(1/2) := by
    norm_num [denominatorReduced,RationalPolynomial3.eval_add,denominator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤denominatorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf001


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf002
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(-49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[-2]], [[1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-258741189173845933053564533251916848613/38440803871216407195144000000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(31/40), (3107/4000)⟩, ⟨(1581/8000), (527/2000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 961020096780410179878600000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[7222389931514331336817632618797921215325], [29025561205739946898260152583426351272606], [20486341273332968287211066524304627573131]], [[13687976536814089656980867737595842430650], [56537515759050747763211510166852702545212], [40215879220451363557767735548609255146262]], [[6468529729346148326339113331297921215325], [27517840801403580877303114008426351272606], [19732481071164785276732547236804627573131]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (31/40) (3107/4000))
    (hr : r∈Icc (1581/8000) (527/2000))
    (hu : u∈Icc 0 1)
    : 0<exclusion p r u := by
  have hx : ∀ i,(exclusionBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [exclusionBox,RatInterval.Contains] using hp
    · simpa [exclusionBox,RatInterval.Contains] using hr
    · simpa [exclusionBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound exclusionChecked ![p, r, u] hx
  have he : exclusionReduced.eval p r u=exclusion p r u-(258741189173845933053564533251916848613/38440803871216407195144000000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(258741189173845933053564533251916848613/38440803871216407195144000000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf002


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf003
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(26985043452482688865520050335381711234370637/15302544925593803520553087500000000000000000)], [(72231088991171301970369970763717217533179971/101813569844322672498559898545312500000000000)], [(-1284496452104125726359432553193271166987/2036271396886453449971197970906250000000)]], [[(-2428466993120438492655624976246597011654659/525489392744891212895793024750000000000000)], [(-49974573088905019894931819367127229/79133998594261900749378468750000000)]], [[(1311345/437443)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-7595488492084667736821136269461815759438893/52548939274489121289579302475000000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(3107/4000), (1557/2000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 105097878548978242579158604950000000000000000000
def numeratorCertificate : DenseBernstein3 := [[[22969833340142445163985160233088176102821336], [410762774890210542777155898833093875711535950], [100097848690046538051816832498542789982801289]], [[37195947573658454975450679129308682621699122], [796386752055662757333007984041657429502778350], [183800618761961183234849492709422927629252578]], [[15190976984169335473642272538923631518877786], [387553702666758865880205592493969803791242400], [84667632822567970845209413853583262646451289]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {p r u : ℝ}
    (hp : p∈Icc (3107/4000) (1557/2000))
    (hr : r∈Icc (527/4000) (1581/8000))
    (hu : u∈Icc 0 1)
    : 0<numerator p r u := by
  have hx : ∀ i,(numeratorBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hp
    · simpa [numeratorBox,RatInterval.Contains] using hr
    · simpa [numeratorBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![p, r, u] hx
  have he : numeratorReduced.eval p r u=numerator p r u-(7595488492084667736821136269461815759438893/52548939274489121289579302475000000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(7595488492084667736821136269461815759438893/52548939274489121289579302475000000000000000000) := by norm_num
  linarith only [hh,hm]

def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
def denominatorReduced : RationalPolynomial3 := denominatorPolynomial.add [[[(-1/2)]]]
def denominatorBox : Fin 3→RatInterval := ![⟨(3107/4000), (1557/2000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def denominatorScale : ℚ := 2
def denominatorCertificate : DenseBernstein3 := [[[1]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u

theorem denominatorChecked : denominatorCertificate.scaledBoxCheck denominatorScale denominatorReduced denominatorBox=true := by
  decide +kernel

theorem denominator_pos {p r u : ℝ}
    (hp : p∈Icc (3107/4000) (1557/2000))
    (hr : r∈Icc (527/4000) (1581/8000))
    (hu : u∈Icc 0 1)
    : 0<denominator p r u := by
  have hx : ∀ i,(denominatorBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [denominatorBox,RatInterval.Contains] using hp
    · simpa [denominatorBox,RatInterval.Contains] using hr
    · simpa [denominatorBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound denominatorChecked ![p, r, u] hx
  have he : denominatorReduced.eval p r u=denominator p r u-(1/2) := by
    norm_num [denominatorReduced,RationalPolynomial3.eval_add,denominator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤denominatorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf003

