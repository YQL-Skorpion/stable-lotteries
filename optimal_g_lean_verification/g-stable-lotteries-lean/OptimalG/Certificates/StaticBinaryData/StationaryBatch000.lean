import OptimalG.Certificates.DenseBernstein


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadShiftLeaf000
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(-108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(-2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[2]], [[-1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-68959115085732869865612338626827152983/60063756048775636242412500000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(31/40), (13/16)⟩, ⟨0, (527/4000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 120127512097551272484825000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[5099943566741934070118899954035084000605], [4579446796467076172734397911126837064496], [137918230171465739731224677253654305966]], [[12227038900130045863419221783070168001210], [13213197126226507791831639572253674128992], [2302988226989109202643871229507308611932]], [[6958166019500930316368536672785084000605], [8295891701985068665233671348626837064496], [1996140682930461985980861396003654305966]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (31/40) (13/16))
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
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadShiftLeaf000


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadShiftLeaf001
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(-132907165445957065758992013149431025402518880213/59965671935147985628428640387500000000000000000)], [(-474444585928090397956365281464079364931691429/3950238638727873553272736685526562500000000000)], [(78684815404761687109510464798083720678813/79004772774557471065454733710531250000000)]], [[(5299621/998367)]], [[(-3148994/998367)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-68099091268916256105607698069360971890274551/29982835967573992814214320193750000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(31/40), (13/16)⟩, ⟨(527/4000), (527/2000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 59965671935147985628428640387500000000000000000
def numeratorCertificate : DenseBernstein3 := [[[136198182537832512211215396138721943780549102], [1396852079134954683845300976778791197584437896], [2297326339554857399301885954354822273747250069]], [[1215428042636722449972335975668068887561098204], [4679767513392024218790412320338832395168875792], [5537684356670772224153677092100269547494500138]], [[813251162171464363876455646369190693780549102], [2750958038402218387175781477239728697584437896], [2974379319188489250967126204585291023747250069]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {p r u : ℝ}
    (hp : p∈Icc (31/40) (13/16))
    (hr : r∈Icc (527/4000) (527/2000))
    (hu : u∈Icc 0 1)
    : 0<numerator p r u := by
  have hx : ∀ i,(numeratorBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hp
    · simpa [numeratorBox,RatInterval.Contains] using hr
    · simpa [numeratorBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![p, r, u] hx
  have he : numeratorReduced.eval p r u=numerator p r u-(68099091268916256105607698069360971890274551/29982835967573992814214320193750000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(68099091268916256105607698069360971890274551/29982835967573992814214320193750000000000000000) := by norm_num
  linarith only [hh,hm]

def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
def denominatorReduced : RationalPolynomial3 := denominatorPolynomial.add [[[(-1/2)]]]
def denominatorBox : Fin 3→RatInterval := ![⟨(31/40), (13/16)⟩, ⟨(527/4000), (527/2000)⟩, ⟨0, 1⟩]
def denominatorScale : ℚ := 2
def denominatorCertificate : DenseBernstein3 := [[[1]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u

theorem denominatorChecked : denominatorCertificate.scaledBoxCheck denominatorScale denominatorReduced denominatorBox=true := by
  decide +kernel

theorem denominator_pos {p r u : ℝ}
    (hp : p∈Icc (31/40) (13/16))
    (hr : r∈Icc (527/4000) (527/2000))
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
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadShiftLeaf001


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadShiftLeaf002
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(-486129273577582691282783367578924400897760239473/117492394992179387771597878800000000000000000000)], [(-6759342395438635879765914678501654269063435009/7739811520109817169454010265950000000000000000)], [(257840661454100849131647341320072809010073/154796230402196343389080205319000000000000)]], [[(4670405/489032)]], [[(-5159437/978064)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-1962184333397474951552681455462667558800333/159528031218166174842631200000000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(13/16), (17/20)⟩, ⟨0, (527/2000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 234984789984358775543195757600000000000000000000
def numeratorCertificate : DenseBernstein3 := [[[29927667104849024122700758497903126390366630545], [5780595046188961207274199567793018628225781018], [3029333658602166583049070845025566307520844673]], [[68475007634367352918461652309946877780733261090], [28800536941716531760668669763867287256451562036], [14678340741873637839158277004191757615041689346]], [[36804180224610052920167896189629688890366630545], [19533621285711018802208474951246143628225781018], [9905846778363195380516208536752128807520844673]]]
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
  have he : numeratorReduced.eval p r u=numerator p r u-(1962184333397474951552681455462667558800333/159528031218166174842631200000000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1962184333397474951552681455462667558800333/159528031218166174842631200000000000000000000) := by norm_num
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
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadShiftLeaf002


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadZeroLeaf000
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(-108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(-2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[2]], [[-1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-68959115085732869865612338626827152983/60063756048775636242412500000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(31/40), (13/16)⟩, ⟨0, (527/4000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 120127512097551272484825000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[5099943566741934070118899954035084000605], [4579446796467076172734397911126837064496], [137918230171465739731224677253654305966]], [[12227038900130045863419221783070168001210], [13213197126226507791831639572253674128992], [2302988226989109202643871229507308611932]], [[6958166019500930316368536672785084000605], [8295891701985068665233671348626837064496], [1996140682930461985980861396003654305966]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (31/40) (13/16))
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
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadZeroLeaf000


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadZeroLeaf001
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(-14241752609746499643825693980713510103928884725755130007102537694729956981022991/60047785260401985026253627016018447051625207442464070901992506250000000000000000)], [(-23650088087559631203133364781042836788637524088728643088408849810038940951773/359604350366270978509496152698201381775073685479301879151705122656250000000000)], [(100144501327157577594907463119053228077/394839085986069753789023869828125000000)]], [[(66575/109769)]], [[(-760501881324209994790980212933155847916/1999468205472841828008468647620637523857)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-2302676816224612434063690264939927994032995976015545658434505419607593582357/30023892630200992513126813508009223525812603721232035450996253125000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(31/40), (13/16)⟩, ⟨(527/4000), (527/2000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 60047785260401985026253627016018447051625207442464070901992506250000000000000000
def numeratorCertificate : DenseBernstein3 := [[[4605353632449224868127380529879855988065991952031091316869010839215187164714], [17640297196688440903555312066829438136445325377573000626022181566061785973272], [277400707493290154853545219631955649903548769138312392277792598581090655099983]], [[47390308216117778619976917745636427086895627970240326110677927928430374329428], [111639796295815539574554937505412306494417938887502288205924175632123571946544], [592981015937799638590812595949788014917861182342802928032525103412181310199966]], [[10667189328166177009252615216230612095994876018527410650806092870465187164714], [29763968588122345185805781439530950352303093510565639293896345628561785973272], [283462543189007106994670454318306406011477653204808711611729680612340655099983]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {p r u : ℝ}
    (hp : p∈Icc (31/40) (13/16))
    (hr : r∈Icc (527/4000) (527/2000))
    (hu : u∈Icc 0 1)
    : 0<numerator p r u := by
  have hx : ∀ i,(numeratorBox i).Contains (![p, r, u] i) := by
    intro i
    fin_cases i
    · simpa [numeratorBox,RatInterval.Contains] using hp
    · simpa [numeratorBox,RatInterval.Contains] using hr
    · simpa [numeratorBox,RatInterval.Contains] using hu
  have hh := DenseBernstein3.scaledBoxCheck_sound numeratorChecked ![p, r, u] hx
  have he : numeratorReduced.eval p r u=numerator p r u-(2302676816224612434063690264939927994032995976015545658434505419607593582357/30023892630200992513126813508009223525812603721232035450996253125000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(2302676816224612434063690264939927994032995976015545658434505419607593582357/30023892630200992513126813508009223525812603721232035450996253125000000000000000) := by norm_num
  linarith only [hh,hm]

def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
def denominatorReduced : RationalPolynomial3 := denominatorPolynomial.add [[[(-1/2)]]]
def denominatorBox : Fin 3→RatInterval := ![⟨(31/40), (13/16)⟩, ⟨(527/4000), (527/2000)⟩, ⟨0, 1⟩]
def denominatorScale : ℚ := 2
def denominatorCertificate : DenseBernstein3 := [[[1]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u

theorem denominatorChecked : denominatorCertificate.scaledBoxCheck denominatorScale denominatorReduced denominatorBox=true := by
  decide +kernel

theorem denominator_pos {p r u : ℝ}
    (hp : p∈Icc (31/40) (13/16))
    (hr : r∈Icc (527/4000) (527/2000))
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
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadZeroLeaf001

