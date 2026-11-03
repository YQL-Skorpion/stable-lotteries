import OptimalG.Certificates.DenseBernstein


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf009
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(-49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[-2]], [[1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-214215926814888553907064147001916848613/38440803871216407195144000000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(3121/4000), (391/500)⟩, ⟨(1581/8000), (527/2000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 961020096780410179878600000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[6091599628262056821099853687547921215325], [26763980599235397866824594720926351272606], [19355550970080693771493287593054627573131]], [[11444054674587880662600579150095842430650], [52049672034598329774450932991852702545212], [37971957358225154563387446961109255146262]], [[5355398170372213847676603675047921215325], [25291577683455711919978094695926351272606], [18619349512190850798070037580554627573131]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (3121/4000) (391/500))
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
  have he : exclusionReduced.eval p r u=exclusion p r u-(214215926814888553907064147001916848613/38440803871216407195144000000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(214215926814888553907064147001916848613/38440803871216407195144000000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyLeftLeaf009


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf000
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(-108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(-2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[2]], [[-1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-162087968839359493859472919876827152983/60063756048775636242412500000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(391/500), (1589/2000)⟩, ⟨0, (527/4000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 120127512097551272484825000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[5286201274249187318106621116535084000605], [4951962211481582668709840236126837064496], [324175937678718987718945839753654305966]], [[11227097489430029071255538483070168001210], [11213314304826474207504272972253674128992], [1303046816289092410480187929507308611932]], [[5922126291415599366823163460285084000605], [6223812245814406766142924923626837064496], [960100954845131036435488183503654305966]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (391/500) (1589/2000))
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
  have he : exclusionReduced.eval p r u=exclusion p r u-(162087968839359493859472919876827152983/60063756048775636242412500000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(162087968839359493859472919876827152983/60063756048775636242412500000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf000


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf001
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(135773668685784477044061258096459696274952650378484715915646275645620312323687739/328024977584943985441214000026321835399860896821228393364148415625000000000000000)], [(83292115574420348562416665893701692816633123/221208212145452432533534469851171875000000000)], [(-1481196371782055884665884194222283940331/4424164242909048650670689397023437500000)]], [[(-250595/223629)], [(-399796584711240159159454554937017832000/1184035566915954989352227223734423920049)]], [[(16200922440542409336663139451702477067128/21845119197578425733342894300511961621701)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-10751231225092011362842762536179571843518220511747475695771127926257247944647/164012488792471992720607000013160917699930448410614196682074207812500000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(391/500), (3153/4000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 1312099910339775941764856000105287341599443587284913573456593662500000000000000000
def numeratorCertificate : DenseBernstein3 := [[[107190986553607590271059983874612622055703056775314418104599083722557983557176], [2311870219812367398579399766992100793366562980517224732658095012668992715043400], [298386640023083531147262058257427005974036091426722513559272799445531437359899]], [[172019699601472181805484200578873149496291528187959611132338046820115967114352], [4356608732053411827333602575274831707143642342167926461613498612212985430086800], [372003845980587091205962924975836226973703149349591248492714306391062874719798]], [[102839972939812797854771520364694156932498811523129943630987646691307983557176], [2120761032024940841394897415603598172760900041871671230161900966731492715043400], [111628465849451766379048170378842850491577398033353485536690190539281437359899]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {p r u : ℝ}
    (hp : p∈Icc (391/500) (3153/4000))
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
  have he : numeratorReduced.eval p r u=numerator p r u-(10751231225092011362842762536179571843518220511747475695771127926257247944647/164012488792471992720607000013160917699930448410614196682074207812500000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(10751231225092011362842762536179571843518220511747475695771127926257247944647/164012488792471992720607000013160917699930448410614196682074207812500000000000000) := by norm_num
  linarith only [hh,hm]

def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
def denominatorReduced : RationalPolynomial3 := denominatorPolynomial.add [[[(-1/2)]]]
def denominatorBox : Fin 3→RatInterval := ![⟨(391/500), (3153/4000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def denominatorScale : ℚ := 2
def denominatorCertificate : DenseBernstein3 := [[[1]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u

theorem denominatorChecked : denominatorCertificate.scaledBoxCheck denominatorScale denominatorReduced denominatorBox=true := by
  decide +kernel

theorem denominator_pos {p r u : ℝ}
    (hp : p∈Icc (391/500) (3153/4000))
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
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf001


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf002
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exclusionPolynomial : RationalPolynomial3 := [[[(108808195000699339505430609743711261693429/120127512097551272484825000000000000000000)], [(2810220168508395983751700998471665468357/7913399859426190074937846875000000000000)], [(-49974573088905019894931819367127229/158267997188523801498756937500000000)]], [[-2]], [[1]]]
def exclusionReduced : RationalPolynomial3 := exclusionPolynomial.add [[[(-162591128490965894556710603251916848613/38440803871216407195144000000000000000000)]]]
def exclusionBox : Fin 3→RatInterval := ![⟨(391/500), (3153/4000)⟩, ⟨(1581/8000), (527/2000)⟩, ⟨0, 1⟩]
def exclusionScale : ℚ := 961020096780410179878600000000000000000000
def exclusionCertificate : DenseBernstein3 := [[[6646018128470280331435442268797921215325], [27872817599651844887495771883426351272606], [19909969470288917281828876174304627573131]], [[10673256493213942922701699537595842430650], [50508075671850454294653173766852702545212], [37201159176851216823488567348609255146262]], [[4064778212274147363917765081297921215325], [22710337767259578952460417508426351272606], [17328729554092784314311198986804627573131]]]
noncomputable def exclusion (p r u : ℝ) : ℝ := exclusionPolynomial.eval p r u

theorem exclusionChecked : exclusionCertificate.scaledBoxCheck exclusionScale exclusionReduced exclusionBox=true := by
  decide +kernel

theorem exclusion_pos {p r u : ℝ}
    (hp : p∈Icc (391/500) (3153/4000))
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
  have he : exclusionReduced.eval p r u=exclusion p r u-(162591128490965894556710603251916848613/38440803871216407195144000000000000000000) := by
    norm_num [exclusionReduced,RationalPolynomial3.eval_add,exclusion,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤exclusionReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(162591128490965894556710603251916848613/38440803871216407195144000000000000000000) := by norm_num
  linarith only [hh,hm]
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf002


namespace OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf003
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numeratorPolynomial : RationalPolynomial3 := [[[(740356889328575602530863645429535507985406324254165809655321448433338587504186783/1778277956238033268806581296039023340936610909333225199447111281250000000000000000)], [(452678695403837950250675251936811288639350631/1199206506447269126693674987746093750000000000)], [(-8050054156880087319735302259114955429007/23984130128945382533873499754921875000000)]], [[(-682499/606165)], [(-399796584711240159159454554937017832000/1184035566915954989352227223734423920049)]], [[(44072216813172835769019188009266053399308/59213012079829210141134627099659852775885)]]]
def numeratorReduced : RationalPolynomial3 := numeratorPolynomial.add [[[(-23294608240272116834722006006362983716402021613960937068922459184361868739951/569048945996170646018106014732487469099715490986632063823075610000000000000000000)]]]
def numeratorBox : Fin 3→RatInterval := ![⟨(3153/4000), (1589/2000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def numeratorScale : ℚ := 14226223649904266150452650368312186727492887274665801595576890250000000000000000000
def numeratorCertificate : DenseBernstein3 := [[[1157846082708684992507930095117486833833943885017273922729464885842990062815113], [23760768010393523265824825566879883995549769868003407286022160409822657354055938], [1882160107368198592225233596960060193805195166775910579288346904296546718498775]], [[2580000295035686316862439121408550758455734212410903587177100511060980125630226], [46072433174169723253211781716774952916512257826658561781580370110895314708111876], [2050909238500757574166018845761728222235261981827212626394572360468093436997550]], [[1835770287201245263281773927648470489101774052691351044064471648655490062815113], [23138897313524687865241485952609882049922455409250597254791881747947657354055938], [582365206006802920868050150159074592910050540349023426723061479609046718498775]]]
noncomputable def numerator (p r u : ℝ) : ℝ := numeratorPolynomial.eval p r u

theorem numeratorChecked : numeratorCertificate.scaledBoxCheck numeratorScale numeratorReduced numeratorBox=true := by
  decide +kernel

theorem numerator_pos {p r u : ℝ}
    (hp : p∈Icc (3153/4000) (1589/2000))
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
  have he : numeratorReduced.eval p r u=numerator p r u-(23294608240272116834722006006362983716402021613960937068922459184361868739951/569048945996170646018106014732487469099715490986632063823075610000000000000000000) := by
    norm_num [numeratorReduced,RationalPolynomial3.eval_add,numerator,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤numeratorReduced.eval p r u at hh
  rw [he] at hh
  have hm : (0:ℝ)<(23294608240272116834722006006362983716402021613960937068922459184361868739951/569048945996170646018106014732487469099715490986632063823075610000000000000000000) := by norm_num
  linarith only [hh,hm]

def denominatorPolynomial : RationalPolynomial3 := [[[1]]]
def denominatorReduced : RationalPolynomial3 := denominatorPolynomial.add [[[(-1/2)]]]
def denominatorBox : Fin 3→RatInterval := ![⟨(3153/4000), (1589/2000)⟩, ⟨(527/4000), (1581/8000)⟩, ⟨0, 1⟩]
def denominatorScale : ℚ := 2
def denominatorCertificate : DenseBernstein3 := [[[1]]]
noncomputable def denominator (p r u : ℝ) : ℝ := denominatorPolynomial.eval p r u

theorem denominatorChecked : denominatorCertificate.scaledBoxCheck denominatorScale denominatorReduced denominatorBox=true := by
  decide +kernel

theorem denominator_pos {p r u : ℝ}
    (hp : p∈Icc (3153/4000) (1589/2000))
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
end OptimalG.Certificates.StaticBinaryData.Stationary.HeadEarlyRightLeaf003

