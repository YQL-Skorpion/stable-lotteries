import OptimalG.Certificates.DenseBernstein


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf004
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(-49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[-2]], [[1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-112467924068262626112417372001916848613/38440803871216407195144000000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(3153/4000), (1589/2000)⟩, ⟨(1581/8000), (527/2000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 961020096780410179878600000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[5317858322841729075025095862547921215325], [25216497988394742374675079070926351272606], [18581809664660366025418529768054627573131]], [[8092016577017809955184022350095842430650], [45345595839458188359617819391852702545212], [34619919260655083855970890161109255146262]], [[2811698101706565652810434300047921215325], [20204177546124415530245755945926351272606], [16075649443525202603203868205554627573131]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (3153/4000) (1589/2000))
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
  have he : exclusionReduced.eval p r u=exclusion p r u-(112467924068262626112417372001916848613/38440803871216407195144000000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(112467924068262626112417372001916848613/38440803871216407195144000000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf004


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf005
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(-108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(-2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[2]], [[-1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-321069223130962506038608505814327152983/60063756048775636242412500000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(1589/2000), (807/1000)⟩, ⟨0, (527/4000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 120127512097551272484825000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[5604163782832393342464892288410084000605], [5587887228647994717426382579876837064496], [642138446261925012077217011628654305966]], [[11825482659065956347320573014320168001210], [12410084644098328759634342034753674128992], [1901431985925019686545222460757308611932]], [[6202548952468320618529926819660084000605], [6784657567919849269556451642376837064496], [1240523615897852288142251542878654305966]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (1589/2000) (807/1000))
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
  have he : exclusionReduced.eval p r u=exclusion p r u-(321069223130962506038608505814327152983/60063756048775636242412500000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(321069223130962506038608505814327152983/60063756048775636242412500000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf005


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf006
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(1473767889714027507672796784848385255961564049861365321469348300185453715725595253/3521514401620202933833985286579674477165965260179873976194689275000000000000000000)], [(742204438484583954872677999005353095182298913/1961776667750955934654183554778125000000000000)], [(-13198734523937615899430547881232605323961/39235533355019118693083671095562500000000)]], [[(-840937/743717)], [(-399796584711240159159454554937017832000/1184035566915954989352227223734423920049)]], [[(1247686554217687157410906496820421065086649/1670943794535167546140550994599799913751579)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-606075457832798818907729378046783259212112238205469017874710915181191953489279/21410807561850833837710630542404420821169068781893633775263710792000000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(1589/2000), (3203/4000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 535270189046270845942765763560110520529226719547340844381592769800000000000000000000
def numeratorCertificate : DenseBernstein3 := [[[62119667947860042491090769706544068988367535965144674313180856454993717175312377], [879685151934789823060845228474431753577816659143914254202353744963321276412248802], [36176928255746664044304425554451632815320864656860304714300904992342298837231975]], [[162014506137070394345648286140967335070167750140706781404741996898737434350624754], [1760507777963947295701018248002652171156663773048288399098137704154142552824497604], [35716160364510668304469895434812732538239505863763067343651740223434597674463950]], [[115507492526266318067085281005231747839184378923796069909078078092181217175312377], [912047934703269405065228548669837381093615443400842070530817834487696276412248802], [15151886445819970472693234451169581480302805955136725446867772879529798837231975]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {p r u : ℝ}
    (hp : p∈Icc (1589/2000) (3203/4000))
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
  have he : numeratorReduced.eval p r u=numerator p r u-(606075457832798818907729378046783259212112238205469017874710915181191953489279/21410807561850833837710630542404420821169068781893633775263710792000000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(606075457832798818907729378046783259212112238205469017874710915181191953489279/21410807561850833837710630542404420821169068781893633775263710792000000000000000000) := by norm_num
  linarith only [hh,hm]

def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
def denominatorReduced : RationalPolynomial3 := denominatorPolynomial.add [[[(-1/2)]]]
def denominatorBox : Fin 3→RatInterval := ![⟨(1589/2000), (3203/4000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def denominatorScale : ℚ := 2
def denominatorCertificate : DenseBernstein3 := [[[1]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u

theorem denominatorChecked : denominatorCertificate.scaledBoxCheck denominatorScale denominatorReduced denominatorBox=true := by
  decide +kernel

theorem denominator_pos {p r u : ℝ}
    (hp : p∈Icc (1589/2000) (3203/4000))
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
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf006


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf007
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(-49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[-2]], [[1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-63846313546778748574184453251916848613/38440803871216407195144000000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(1589/2000), (3203/4000)⟩, ⟨(1581/8000), (527/2000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 961020096780410179878600000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[4027238364743662591266257268797921215325], [22635258072198609407157401883426351272606], [17291189706562299541659691174304627573131]], [[5585856355882646532969360787595842430650], [40333275397187861515188496266852702545212], [32113759039519920433756228598609255146262]], [[1596157838669468714354611331297921215325], [17773097020050221653334110008426351272606], [14860109180488105664748045236804627573131]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (1589/2000) (3203/4000))
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
  have he : exclusionReduced.eval p r u=exclusion p r u-(63846313546778748574184453251916848613/38440803871216407195144000000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(63846313546778748574184453251916848613/38440803871216407195144000000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf007


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf008
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(4662378291014138452677634619911785812147548558560573967602066081810062936131953451/11123484541756249856032024466839310342962539963834426364447470611250000000000000000)], [(123472643543753394338098486769849565683201509/326142466136398026438984674213906250000000000)], [(-2195732817807219859123619347533469060573/6522849322727960528779693484278125000000)]], [[(-933201/824279)], [(-399796584711240159159454554937017832000/1184035566915954989352227223734423920049)]], [[(1384155518717375956985124032740050617654380/1851946210743674502216820690232613310045673)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-94385749999354259595466854883857847339015096906708194710788965219979580818747/3559515053361999953930247829388579309748012788427016436623190595600000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(3203/4000), (807/1000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 88987876334049998848256195734714482743700319710675410915579764890000000000000000000
def numeratorCertificate : DenseBernstein3 := [[[18526760293714159456892249125278417384531986383036057449177935346176501871506461], [151406294209352531315284475553283983574979699549126119260772953781257495898378986], [2888246329221428131451084288590628392796465784603146093621188161436989520468675]], [[48367344280056897505243576305107656740106946490364759145391390317978003743012922], [313069206952858497938899203328130424702360196098674000316878499126264991796757972], [4719287499967712979773342744192892366950754845335409735539448260998979040937350]], [[32438633342899205814742186610028251172289933350646287103645404713989001871506461], [166859011456618902156396446635244464760810443036183051870969444829382495898378986], [4429090527302752614713117885801275790869262304049849049350209841749489520468675]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {p r u : ℝ}
    (hp : p∈Icc (3203/4000) (807/1000))
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
  have he : numeratorReduced.eval p r u=numerator p r u-(94385749999354259595466854883857847339015096906708194710788965219979580818747/3559515053361999953930247829388579309748012788427016436623190595600000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(94385749999354259595466854883857847339015096906708194710788965219979580818747/3559515053361999953930247829388579309748012788427016436623190595600000000000000000) := by norm_num
  linarith only [hh,hm]

def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
def denominatorReduced : RationalPolynomial3 := denominatorPolynomial.add [[[(-1/2)]]]
def denominatorBox : Fin 3→RatInterval := ![⟨(3203/4000), (807/1000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def denominatorScale : ℚ := 2
def denominatorCertificate : DenseBernstein3 := [[[1]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u

theorem denominatorChecked : denominatorCertificate.scaledBoxCheck denominatorScale denominatorReduced denominatorBox=true := by
  decide +kernel

theorem denominator_pos {p r u : ℝ}
    (hp : p∈Icc (3203/4000) (807/1000))
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
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf008

