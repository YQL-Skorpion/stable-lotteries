import OptimalG.Certificates.DenseBernstein


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf004
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(-49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[-2]], [[1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-243781710092337873091029276001916848613/38440803871216407195144000000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(3107/4000), (1557/2000)⟩, ⟨(1581/8000), (527/2000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 961020096780410179878600000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[6842516706383849825402494762547921215325], [28265814755478983875429876870926351272606], [20106468048202486775795928668054627573131]], [[12934116334645906646502348450095842430650], [55029795354714381742254471591852702545212], [39462019018283180547289216261109255146262]], [[6094542752308446827275731900047921215325], [26769866847328177879176351145926351272606], [19358494094127083777669165805554627573131]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (3107/4000) (1557/2000))
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
  have he : exclusionReduced.eval p r u=exclusion p r u-(243781710092337873091029276001916848613/38440803871216407195144000000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(243781710092337873091029276001916848613/38440803871216407195144000000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf004


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf005
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(-108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(-2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[2]], [[-1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-115891432468344932634527405814327152983/60063756048775636242412500000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(1557/2000), (391/500)⟩, ⟨0, (527/4000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 120127512097551272484825000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[5193808201507158195656730088410084000605], [4767176065997524423810058179876837064496], [231782864936689865269054811628654305966]], [[10573874110521569639301181339320168001210], [9906867547009555343595558684753674128992], [649823437380632978525830785757308611932]], [[5378594346991216440556512144660084000605], [5136748356965640913609622292376837064496], [416569010420748110168836867878654305966]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (1557/2000) (391/500))
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
  have he : exclusionReduced.eval p r u=exclusion p r u-(115891432468344932634527405814327152983/60063756048775636242412500000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(115891432468344932634527405814327152983/60063756048775636242412500000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf005


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf006
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(12340338260464719166975944634555574119419762239/7031450360608656977081480575000000000000000000)], [(327084335632860716944844230913115615527539587/463196792505095278365242532878125000000000000)], [(-5816590536390744170591009387959305310539/9263935850101905567304850657562500000000)]], [[(-2912769192694208149290042821821962082243087/632830532454779127937333251750000000000000)], [(-49974573088905019894931819367127229/79133998594261900749378468750000000)]], [[(1574318/526799)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-5831573481616212838351922624808887682857689/42188702163651941862488883450000000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(1557/2000), (3121/4000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 253132212981911651174933300700000000000000000000
def numeratorCertificate : DenseBernstein3 := [[[47261405243847275457985924975385843621266434], [912660734795180066567808019255929073400340900], [175697106698800301081993156103268602581912541]], [[79934139552312241616699342850951669718412568], [1777715539129532061634129893054669831775461500], [318376953872154839961772673849168907662725082]], [[34989440889697277030111535748853326097146134], [869688217496816616809118109545315758375120600], [144996553754586849751177635619187805080812541]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {p r u : ℝ}
    (hp : p∈Icc (1557/2000) (3121/4000))
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
  have he : numeratorReduced.eval p r u=numerator p r u-(5831573481616212838351922624808887682857689/42188702163651941862488883450000000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(5831573481616212838351922624808887682857689/42188702163651941862488883450000000000000000000) := by norm_num
  linarith only [hh,hm]

def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
def denominatorReduced : RationalPolynomial3 := denominatorPolynomial.add [[[(-1/2)]]]
def denominatorBox : Fin 3→RatInterval := ![⟨(1557/2000), (3121/4000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def denominatorScale : ℚ := 2
def denominatorCertificate : DenseBernstein3 := [[[1]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u

theorem denominatorChecked : denominatorCertificate.scaledBoxCheck denominatorScale denominatorReduced denominatorBox=true := by
  decide +kernel

theorem denominator_pos {p r u : ℝ}
    (hp : p∈Icc (1557/2000) (3121/4000))
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
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf006


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf007
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(-49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[-2]], [[1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-228939955972685413375529147251916848613/38440803871216407195144000000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(1557/2000), (3121/4000)⟩, ⟨(1581/8000), (527/2000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 961020096780410179878600000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[6465586605299758320163235118797921215325], [27511954553310800864951357583426351272606], [19729537947118395270556669024304627573131]], [[12186142380570503648375585587595842430650], [53533847446563575746000945866852702545212], [38714045064207777549162453398609255146262]], [[5723498899317135334388228681297921215325], [26027779141345554893401344708426351272606], [18987450241135772284781662586804627573131]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (1557/2000) (3121/4000))
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
  have he : exclusionReduced.eval p r u=exclusion p r u-(228939955972685413375529147251916848613/38440803871216407195144000000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(228939955972685413375529147251916848613/38440803871216407195144000000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf007


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf008
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(96908516286859636417283460873090512035403324459/55345387628608017361753543650000000000000000000)], [(2568740759648638025263901083373993726326551347/3645877410034553143705514687943750000000000000)], [(-45680307997948500440380223060729353339259/72917548200691062874110293758875000000000)]], [[(-13669227917688882835089651816785434440301/2975558474656345019449115250000000000000)], [(-49974573088905019894931819367127229/79133998594261900749378468750000000)]], [[(1374793/460722)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-3740890229391570732289001986449093292280357/27672693814304008680876771825000000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(3121/4000), (391/500)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 221381550514432069447014174600000000000000000000
def numeratorCertificate : DenseBernstein3 := [[[35850563186530362728945421259958788144506256], [753401292997512647725627506019192947302878800], [115712671938010791694672645934124928913635219]], [[63754591853108600706980369452795284482749112], [1474792447271254496946211121526418197153694200], [207361739672202909635211874423404452181470438]], [[29927121835132565858312015891592746338242856], [725437340610850504981137750904737749850815400], [93672160902746445820816296188035773267835219]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {p r u : ℝ}
    (hp : p∈Icc (3121/4000) (391/500))
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
  have he : numeratorReduced.eval p r u=numerator p r u-(3740890229391570732289001986449093292280357/27672693814304008680876771825000000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(3740890229391570732289001986449093292280357/27672693814304008680876771825000000000000000000) := by norm_num
  linarith only [hh,hm]

def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
def denominatorReduced : RationalPolynomial3 := denominatorPolynomial.add [[[(-1/2)]]]
def denominatorBox : Fin 3→RatInterval := ![⟨(3121/4000), (391/500)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def denominatorScale : ℚ := 2
def denominatorCertificate : DenseBernstein3 := [[[1]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u

theorem denominatorChecked : denominatorCertificate.scaledBoxCheck denominatorScale denominatorReduced denominatorBox=true := by
  decide +kernel

theorem denominator_pos {p r u : ℝ}
    (hp : p∈Icc (3121/4000) (391/500))
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
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf008

