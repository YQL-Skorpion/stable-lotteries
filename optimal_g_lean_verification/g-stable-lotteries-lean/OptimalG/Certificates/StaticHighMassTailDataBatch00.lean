import OptimalG.Certificates.ScaledTensorReconstruction
import OptimalG.Certificates.StaticHighMassTailModelBatch00
import OptimalG.Certificates.StaticHighMassTailModelBatch01
import OptimalG.Certificates.StaticHighMassTailModelBatch02
import OptimalG.Certificates.StaticHighMassTailModelBatch03
import OptimalG.Certificates.StaticHighMassTailModelBatch04


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadSquareLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-3748486330224668047419750275730820634649645106860477961/7063707732453334912712256400000000000000000000000000000000)]], [[(-5923048648355923937072301846803874876316751286037044624198543907679209117/70505593879699676986236872315697870277772250000000000000000000000000000000)], [(2096293009122325873347389227381545925482744735474578478763662799294799/8460671265563961238348424677883744433332670000000000000000000000000000)], [(-6727334798802630415283596669242861937796177056950302430822044089121/36098864066406234616953278625637309582219392000000000000000000000000)]], [[(387716622131186393710304217619889899120778187090311808683466171371768049769117061/105095907779965740607549800257342108349005387773311750000000000000000000000000000)], [(-108918545378128011172874967129245092362828926591/10066730921974369508609334263850000000000000000)], [(1279128737326491306774274353111849802826856119/128854155801271929710199478577280000000000000)], [(-3474682092298477128274714468776989105141/1288541558012719297101994785772800000000)]], [[(-14306980093391990385304774909775583892790080279/5033365460987184754304667131925000000000000000)], [(1358262327133038672681363946330928401953883/201334618439487390172186685277000000000000)], [(-3474682092298477128274714468776989105141/859027705341812864734663190515200000000)]], [[(10407573791774069520242584992127229/158267997188523801498756937500000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-2245389120112336627285363684724238825442342039401782205485244317523183558770529641/3956551822304592587578345421452879373139026363230560000000000000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 3363069048958903699441593608234947467168172408745976000000000000000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨3060505601220428286001832276711934879634800540275128749140075953475135650861203797975, 0, 4, 0, 3, 0, 0⟩,
  ⟨12180530253504059220520766348846132459762739616760948496387195988400746369479937400175, 0, 4, 1, 2, 0, 0⟩,
  ⟨14313715730362423124055503079340321557643132209224133915073851678578519868573683797050, 0, 4, 2, 1, 0, 0⟩,
  ⟨1908580752095486133192559132015603001625990733491514874662457669894706024954950194850, 0, 4, 3, 0, 0, 0⟩,
  ⟨28601540647643657140895303797890103174974248269758574919525060000122609317762298336166, 1, 3, 0, 3, 0, 0⟩,
  ⟨96402691115509007561565062807823261066728360396518651231705328169639212417457299083998, 1, 3, 1, 2, 0, 0⟩,
  ⟨97085559224678532090899502794482530187418253283066729062688687528542174021148245478248, 1, 3, 2, 1, 0, 0⟩,
  ⟨14809707258942122369661675657556061411130793969471524788012295265420195921453244730416, 1, 3, 3, 0, 0, 0⟩,
  ⟨73986847358963373129475650267625683712381374421160466115123432958094301142786733688296, 2, 2, 0, 3, 0, 0⟩,
  ⟨234150743267141579700315592386562939018804336977772788586118177031425547544693457253888, 2, 2, 1, 2, 0, 0⟩,
  ⟨219125346684109228698889585850424680366589750959229841404996514482968530891403818055388, 2, 2, 2, 1, 0, 0⟩,
  ⟨35112529510833223464466923387294832137679728190008371679146156031207625739497094489796, 2, 2, 3, 0, 0, 0⟩,
  ⟨75452796815829060130604581521462238102906624958012278419963549846324230658291387559994, 3, 1, 0, 3, 0, 0⟩,
  ⟨230696470142337503717231113111209796188276462095048755033492714622652098322614766856482, 3, 1, 1, 2, 0, 0⟩,
  ⟨206603279399201544716219294943343754712613550618358167968486694805023767041337634864232, 3, 1, 2, 1, 0, 0⟩,
  ⟨33945426732177457478755487545428859532312825019621583560077577657619894377014255567744, 3, 1, 3, 0, 0, 0⟩,
  ⟨27074125518102499736396429466191514080698613641863941897514055289222748206405748409889, 4, 0, 0, 3, 0, 0⟩,
  ⟨80969310781641623999081897257154359960939492023619719449559532835501051897898671286417, 4, 0, 1, 2, 0, 0⟩,
  ⟨70451199253849176625295788881591657160300666859556971977971879235054925374508378490042, 4, 0, 2, 1, 0, 0⟩,
  ⟨11801164743004454131131707374851277198971815441121905216570213576283103558015455613514, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(2245389120112336627285363684724238825442342039401782205485244317523183558770529641/3956551822304592587578345421452879373139026363230560000000000000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(2245389120112336627285363684724238825442342039401782205485244317523183558770529641/3956551822304592587578345421452879373139026363230560000000000000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadSquare.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadSquare.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadSquareLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0CapFlatLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-470272463196815730653662341750276712969/2672893893857100776000000000000000000000)], [(47284303827534513663328459687070859/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(65329043794025186891366123589499445919425055330669/10245695027253913855429055761874000000000000000000)], [(-1853030922623433331961472448582379363679806069/100667309219743695086093342638500000000000000)], [(3314077199103694962452914920959907799034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-418545495632493530650371668937675727257693931/100667309219743695086093342638500000000000000)], [(129400413613291329286209694977407893528897/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-16793704937697490595381060191973869830949478416747769/11803040671396508761454272237678848000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 23606081342793017522908544475357696000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨183899495309660642384805526159500784916689637092808663, 0, 3, 0, 3, 0, 0⟩,
  ⟨369702657702027470688969276671787072278895327753452239, 0, 3, 1, 2, 0, 0⟩,
  ⟨275565010238103001388462577361495381977229647494139114, 0, 3, 2, 1, 0, 0⟩,
  ⟨33587409875394981190762120383947739661898956833495538, 0, 3, 3, 0, 0, 0⟩,
  ⟨954203057789409317845775334190999423879921050599814021, 1, 2, 0, 3, 0, 0⟩,
  ⟨2135375196936885966083714554659437720322250776777503853, 1, 2, 1, 2, 0, 0⟩,
  ⟨1585245563551839109579578920453282775631737040810685118, 1, 2, 2, 1, 0, 0⟩,
  ⟨224142378474746520538034434045345800708782314632995286, 1, 2, 3, 0, 0, 0⟩,
  ⟨1457183005770942861730992235624863820662831956925898629, 2, 1, 0, 3, 0, 0⟩,
  ⟨3426908413916951868707194689343183707211337541580863597, 2, 1, 1, 2, 0, 0⟩,
  ⟨2549125839170035575842878923151469089211152780697288382, 2, 1, 2, 1, 0, 0⟩,
  ⟨388061653075818262940076056949935910560772196042323414, 2, 1, 3, 0, 0, 0⟩,
  ⟨695451236463896487339834243058397854557707340914050007, 3, 0, 0, 3, 0, 0⟩,
  ⟨1686951254200200276521884857750631077742302485042282191, 3, 0, 1, 2, 0, 0⟩,
  ⟨1265160665374406370861198026454779714130965779866212586, 3, 0, 2, 1, 0, 0⟩,
  ⟨206078477649169024662615558753570522371995635737980402, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(16793704937697490595381060191973869830949478416747769/11803040671396508761454272237678848000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(16793704937697490595381060191973869830949478416747769/11803040671396508761454272237678848000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapFlat.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapFlat.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0CapFlatLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadZeroTriangleLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-334011696534700096000063783977069004491/171065209206854449664000000000000000000000)], [(213917588184878543033584931991170787359/6842608368274177986560000000000000000000)], [(-604043364215083767745681126996388986863/5474086694619342389248000000000000000000)]], [[(15920900083946846726997837890616104948695427/1610676947515899121377493482216000000000000000)], [(-3835658377880134343046068523970422760771314631001/5726851368945419098231087936768000000000000000000)], [(266011698316739662863980912082385291106570397270037/103083324641017543768159582861824000000000000000000)], [(127187770426943/130264268800000)]], [[(-569075869505738793193760632557915844486263/2796314144992880419058148406625000000000000)], [(212271766452422941829471875511806916921822717/100667309219743695086093342638500000000000000)], [(-1025661477282925859515216069150777171428571878851/103083324641017543768159582861824000000000000000)], [(-311989624923/65132134400)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)], [(-90293174783179465068224881133604962787463/50333654609871847543046671319250000000000)], [(2772242281137553832044114653510860365028051/201334618439487390172186685277000000000000)], [(1275509505/162830336)]], [[], [], [(-130366875/20353792)], [(-43455625/10176896)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-24459891497992154256122947369655908558859/8399301772056553478502400000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (1413/2000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 412333298564070175072638331447296000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨3930552761187324670440265074686149250347641408681516, 0, 4, 0, 3, 0, 0⟩,
  ⟨9387393364002848365331081854006643064867748058749648, 0, 4, 1, 2, 0, 0⟩,
  ⟨7507001870838290510967294380315880173473390179663073, 0, 4, 2, 1, 0, 0⟩,
  ⟨1984852029875421377332540636874793424515783529594941, 0, 4, 3, 0, 0, 0⟩,
  ⟨19891415740855248592113323841872209800910593229452464, 1, 3, 0, 3, 0, 0⟩,
  ⟨45344565455051941973586122554015749899345040111056124, 1, 3, 1, 2, 0, 0⟩,
  ⟨34565428665765159698808343262351504151876564256152718, 1, 3, 2, 1, 0, 0⟩,
  ⟨8557834836814697074677838495795936118597742374549058, 1, 3, 3, 0, 0, 0⟩,
  ⟨36701187472316828138539717314630200332240008281524488, 2, 2, 0, 3, 0, 0⟩,
  ⟨79711221481541445873725569678556940358312283240673812, 2, 2, 1, 2, 0, 0⟩,
  ⟨57700725943413156527784483201874502792694502879518977, 2, 2, 2, 1, 0, 0⟩,
  ⟨12972261977395165537697303076162727101053477920369653, 2, 2, 3, 0, 0, 0⟩,
  ⟨29475782025606413455534790205780279142217892213576880, 3, 1, 0, 3, 0, 0⟩,
  ⟨60881239269266583799296747929524387870506778087337076, 3, 1, 1, 2, 0, 0⟩,
  ⟨41328217333146836267192609516336363280541461209232092, 3, 1, 2, 1, 0, 0⟩,
  ⟨7644904158541875126950293388879562034940075335471896, 3, 1, 3, 0, 0, 0⟩,
  ⟨8735457532957509238668131658336139360540835752823340, 4, 0, 0, 3, 0, 0⟩,
  ⟨17127189878774231533826218950976554346671786898969740, 4, 0, 1, 2, 0, 0⟩,
  ⟨10659005060016146602614998249940378988538569906202760, 4, 0, 2, 1, 0, 0⟩,
  ⟨1200769780345314745541326594042801831782618760056360, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p u dummy : ℝ) : ℝ := nPolynomial.eval p u dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p u dummy : ℝ}
    (hp : p∈Icc (13/20) (1413/2000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p u dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hu
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, u, dummy] hx
  have he : nReduced.eval p u dummy=n p u dummy-(24459891497992154256122947369655908558859/8399301772056553478502400000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(24459891497992154256122947369655908558859/8399301772056553478502400000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (1413/2000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p u dummy : ℝ) : ℝ := dPolynomial.eval p u dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p u dummy : ℝ}
    (hp : p∈Icc (13/20) (1413/2000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p u dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hu
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, u, dummy] hx
  have he : dReduced.eval p u dummy=d p u dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (1413/2000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadZeroTriangle.numerator p u dummy := by
  exact n_pos hp hu hdummy

theorem denominator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (1413/2000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadZeroTriangle.denominator p u dummy := by
  exact d_pos hp hu hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadZeroTriangleLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadZeroRectangleLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-489544945756025172411070274336836181369/2672893893857100776000000000000000000000)], [(49747240895804090884722444682158331/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(20767131110825717/3180280000000000)], [(-3664513897785146743365369124120365120400691/191019562086800180429019625500000000000000)], [(3451838563421909209956520099638152845496801/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-675772349176554871232007964386238942099309/191019562086800180429019625500000000000000)], [(118471949899748529291139881557533512721103/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-24459891497992154256122947369655908558859/8399301772056553478502400000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(1413/2000), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 103083324641017543768159582861824000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨2183864383239377309667032914584034840135208938205835, 0, 3, 0, 3, 0, 0⟩,
  ⟨4281797469693557883456554737744138586667946724742435, 0, 3, 1, 2, 0, 0⟩,
  ⟨2664751265004036650653749562485094747134642476550690, 0, 3, 2, 1, 0, 0⟩,
  ⟨300192445086328686385331648510700457945654690014090, 0, 3, 3, 0, 0, 0⟩,
  ⟨8377640194053899956367908921987073598484748651907745, 1, 2, 0, 3, 0, 0⟩,
  ⟨17197414423588239432584142627462392235652174392837225, 1, 2, 1, 2, 0, 0⟩,
  ⟨11001404942245559625608842420373637181292212518591590, 1, 2, 2, 1, 0, 0⟩,
  ⟨1353260599544280839978345559431414451937286777662110, 1, 2, 3, 0, 0, 0⟩,
  ⟨10510188548447728671594580085718726930781575942688673, 2, 1, 0, 3, 0, 0⟩,
  ⟨22368801567920818063204082232346084300516640822422889, 2, 1, 1, 2, 0, 0⟩,
  ⟨14693815867671458765372403414925456151983083169010534, 2, 1, 2, 1, 0, 0⟩,
  ⟨1978339822255072926371063229807162225841768289276318, 2, 1, 3, 0, 0, 0⟩,
  ⟨4331590517698510346866721196828822331182839469970827, 3, 0, 0, 3, 0, 0⟩,
  ⟨9498717954222049479995545698167233127784822877280291, 3, 0, 1, 2, 0, 0⟩,
  ⟨6402695530625848756336361912576316194077922849921826, 3, 0, 2, 1, 0, 0⟩,
  ⟨940449447862425094751066437399582390600939442612362, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (1413/2000) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(24459891497992154256122947369655908558859/8399301772056553478502400000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(24459891497992154256122947369655908558859/8399301772056553478502400000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(1413/2000), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (1413/2000) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (1413/2000:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadZeroRectangle.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (1413/2000:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadZeroRectangle.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadZeroRectangleLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadCapBoundaryTriangleLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-2743749324129654449411938703170651609291/171065209206854449664000000000000000000000)], [(310307093288676717170059928758914091551/6842608368274177986560000000000000000000)], [(-604043364215083767745681126996388986863/5474086694619342389248000000000000000000)]], [[(85962100509340829714697117638958270597295349/8053384737579495606887467411080000000000000000)], [(-7124726436438107165749425252324174724666893797899/17180554106836257294693263810304000000000000000000)], [(239636828852378923253827968684083494613759223560213/103083324641017543768159582861824000000000000000000)], [(127187770426943/130264268800000)]], [[(-228453127507040163677364274879517484098431/4194471217489320628587222609937500000000000)], [(22605367185959459370859733715016704045390269/20133461843948739017218668527700000000000000)], [(-939398617219603734870398592786748401214962152899/103083324641017543768159582861824000000000000000)], [(-311989624923/65132134400)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)], [(-46579319929008265087945627454107439556287/50333654609871847543046671319250000000000)], [(2634480916819339584540509474832615318565699/201334618439487390172186685277000000000000)], [(1275509505/162830336)]], [[], [], [(-130366875/20353792)], [(-43455625/10176896)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-24459891497992154256122947369655908558859/8399301772056553478502400000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (1413/2000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 412333298564070175072638331447296000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨3435924117341384937330729628182357558049864493174316, 0, 4, 0, 3, 0, 0⟩,
  ⟨8669962832856376887715796595737826872494369078397648, 0, 4, 1, 2, 0, 0⟩,
  ⟨7284199983537758766461544568550855673397788114818273, 0, 4, 2, 1, 0, 0⟩,
  ⟨1984852029875421377332540636874793424515783529594941, 0, 4, 3, 0, 0, 0⟩,
  ⟨17004822478800236210229739377227289800295961938111664, 1, 3, 0, 3, 0, 0⟩,
  ⟨41480143156741355977027640202583194595220262290666748, 1, 3, 1, 2, 0, 0⟩,
  ⟨33587599629509586084133445375563868848366417727104142, 1, 3, 2, 1, 0, 0⟩,
  ⟨8557834836814697074677838495795936118597742374549058, 1, 3, 3, 0, 0, 0⟩,
  ⟨30732465668181431116255902703129450583899001108410632, 2, 2, 0, 3, 0, 0⟩,
  ⟨72523879892449670871582948896302451413433619738366484, 2, 2, 1, 2, 0, 0⟩,
  ⟨56482106158456778547925677031120763596156846550325505, 2, 2, 2, 1, 0, 0⟩,
  ⟨12972261977395165537697303076162727101053477920369653, 2, 2, 3, 0, 0, 0⟩,
  ⟨24205901765507126650823850523322695436062484671024304, 3, 1, 0, 3, 0, 0⟩,
  ⟨55253583653787772473582501858270277997536089214164084, 3, 1, 1, 2, 0, 0⟩,
  ⟨40970441977767311746189303127539837113726179878611676, 3, 1, 2, 1, 0, 0⟩,
  ⟨7644904158541875126950293388879562034940075335471896, 3, 1, 3, 0, 0, 0⟩,
  ⟨7042334458784546807466957569238177094409581007551020, 4, 0, 0, 3, 0, 0⟩,
  ⟨15539884085223080691311396568813194306828362688066700, 4, 0, 1, 2, 0, 0⟩,
  ⟨10764822340637958191301349956874981214826400440572040, 4, 0, 2, 1, 0, 0⟩,
  ⟨1200769780345314745541326594042801831782618760056360, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p u dummy : ℝ) : ℝ := nPolynomial.eval p u dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p u dummy : ℝ}
    (hp : p∈Icc (13/20) (1413/2000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p u dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hu
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, u, dummy] hx
  have he : nReduced.eval p u dummy=n p u dummy-(24459891497992154256122947369655908558859/8399301772056553478502400000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(24459891497992154256122947369655908558859/8399301772056553478502400000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (1413/2000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p u dummy : ℝ) : ℝ := dPolynomial.eval p u dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p u dummy : ℝ}
    (hp : p∈Icc (13/20) (1413/2000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p u dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hu
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, u, dummy] hx
  have he : dReduced.eval p u dummy=d p u dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (1413/2000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadCapBoundaryTriangle.numerator p u dummy := by
  exact n_pos hp hu hdummy

theorem denominator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (1413/2000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadCapBoundaryTriangle.denominator p u dummy := by
  exact d_pos hp hu hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadCapBoundaryTriangleLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadCapBoundaryRectangleLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-473320347818799332465137398181697459569/2672893893857100776000000000000000000000)], [(47284303827534513663328459687070859/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(42798588816288963888393249615692967/6682234734642751940000000000000000)], [(-6684359632556589821686560196287265386689/362465962214042088100606500000000000000)], [(3314077199103694962452914920959907799034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-1503722757683952286142384306268672113311/362465962214042088100606500000000000000)], [(129400413613291329286209694977407893528897/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-24459891497992154256122947369655908558859/8399301772056553478502400000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(1413/2000), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 103083324641017543768159582861824000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨1760583614696136701866739392309544273602395251887755, 0, 3, 0, 3, 0, 0⟩,
  ⟨3884971021305770172827849142203298576707090672016675, 0, 3, 1, 2, 0, 0⟩,
  ⟨2691205585159489547825337489218745303706600110143010, 0, 3, 2, 1, 0, 0⟩,
  ⟨300192445086328686385331648510700457945654690014090, 0, 3, 3, 0, 0, 0⟩,
  ⟨6605819088589052024705618492853703515891149789371553, 1, 2, 0, 3, 0, 0⟩,
  ⟨15072062563889251465844907734962264334343817337163369, 1, 2, 1, 2, 0, 0⟩,
  ⟨10668898410871805840389317835621517436484641707940454, 1, 2, 2, 1, 0, 0⟩,
  ⟨1374284822404667089835765438046052525844474160148638, 1, 2, 3, 0, 0, 0⟩,
  ⟨8094509840778227445411997495528134427677598838347681, 2, 1, 0, 3, 0, 0⟩,
  ⟨18931421228141960837130779228605808703279551853576553, 2, 1, 1, 2, 0, 0⟩,
  ⟨13620764320477685213233337350737157456191843930248038, 2, 1, 2, 1, 0, 0⟩,
  ⟨1926989907170655374122717579168546624183640915019166, 2, 1, 3, 0, 0, 0⟩,
  ⟨3256278514048515050183484326719197264302041059879819, 3, 0, 0, 3, 0, 0⟩,
  ⟨7765342127048088326944818431052509182382415465477667, 3, 0, 1, 2, 0, 0⟩,
  ⟨5664083936254977703500454799540051560153392609498402, 3, 0, 2, 1, 0, 0⟩,
  ⟨859901677015519898282649721368416635198018203900554, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (1413/2000) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(24459891497992154256122947369655908558859/8399301772056553478502400000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(24459891497992154256122947369655908558859/8399301772056553478502400000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(1413/2000), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (1413/2000) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (1413/2000:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadCapBoundaryRectangle.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (1413/2000:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadCapBoundaryRectangle.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadCapBoundaryRectangleLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0CapZeroRectangleLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-81677420612452142312958852841103555802630147/1050573335467750000000000000)], [(20944927441142773987972480192613695355371611/1050573335467750000000000000)], [(-70701503796973229766801628802337758746233/42022933418710000000000000)], [(391850844808472366825719533313500799653/8404586683742000000000000)]], [[(729995935348161524179679085143745301873907/262643333866937500000000)], [(-3882043341363562997194145795750389990953/5252866677338750000000)], [(144465546148494981356736620971699705047/2101146670935500000000)], [(-26182914145832169/10)], [33394639989645]], [[(-25872795784469181685099363796613310431/2101146670935500000)], [(5089454774157955961495329556502320253/2101146670935500000)], [-152344835896235400], [3035876362695000]], [[19332719318713200000], [-2516052392211600000], [81774447480000000]], [[-10241621700000000000], [688337100000000000]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-18378708427435069830919845421998250835151/13132166693346875000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (657/1000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 1050573335467750000000000000
def nCertificate : TensorBernstein3 := [
  ⟨6316704475274013332525005376812540453965973, 0, 4, 0, 4, 0, 0⟩,
  ⟨19864386594118584318785441775928311793595503, 0, 4, 1, 3, 0, 0⟩,
  ⟨22848865466916782336070602134778652828609846, 0, 4, 2, 2, 0, 0⟩,
  ⟨10979936808744721704882820798077969692253700, 0, 4, 3, 1, 0, 0⟩,
  ⟨1701557747580943291453955504102588203273384, 0, 4, 4, 0, 0, 0⟩,
  ⟨25454107585856631651293274155934467807283288, 1, 3, 0, 4, 0, 0⟩,
  ⟨80036857296403462483506156893735482303875396, 1, 3, 1, 3, 0, 0⟩,
  ⟨91821073141187846417100391729491429722067660, 1, 3, 2, 2, 0, 0⟩,
  ⟨43791964449146201880336190004176209161468784, 1, 3, 3, 1, 0, 0⟩,
  ⟨6645103750767162703365681399377043935993232, 1, 3, 4, 0, 0, 0⟩,
  ⟨38432374327996957796849745157026134592494526, 2, 2, 0, 4, 0, 0⟩,
  ⟨120767316477206168125714896927917778574013670, 2, 2, 1, 3, 0, 0⟩,
  ⟨138077914831724805930576318727248986099782404, 2, 2, 2, 2, 0, 0⟩,
  ⟨65264126425583973177020164316228575447241652, 2, 2, 3, 1, 0, 0⟩,
  ⟨9658716218403709180772195870419983328978392, 2, 2, 4, 0, 0, 0⟩,
  ⟨25766614891549881167882133872558927579003080, 3, 1, 0, 4, 0, 0⟩,
  ⟨80870830062658748754253035908848257410783164, 3, 1, 1, 3, 0, 0⟩,
  ⟨92071542885470284268867698390406594347801212, 3, 1, 2, 2, 0, 0⟩,
  ⟨43060864799714232919280638167498902179091752, 3, 1, 3, 1, 0, 0⟩,
  ⟨6185490986871281969484439440555387663070624, 3, 1, 4, 0, 0, 0⟩,
  ⟨6471617840396759096901449024479720339825869, 4, 0, 0, 4, 0, 0⟩,
  ⟨20275882689062124400410846856562649347049387, 4, 0, 1, 3, 0, 0⟩,
  ⟨22965685934423234798172398352395385141476622, 4, 0, 2, 2, 0, 0⟩,
  ⟨10608667888415997482363489092243566201065184, 4, 0, 3, 1, 0, 0⟩,
  ⟨1470296674194805586473587633759860066812080, 4, 0, 4, 0, 0, 0⟩]
noncomputable def n (p u dummy : ℝ) : ℝ := nPolynomial.eval p u dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p u dummy : ℝ}
    (hp : p∈Icc (13/20) (657/1000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p u dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hu
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, u, dummy] hx
  have he : nReduced.eval p u dummy=n p u dummy-(18378708427435069830919845421998250835151/13132166693346875000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(18378708427435069830919845421998250835151/13132166693346875000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[959396339712000000], [-64480813056000000]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[-447457763328000000]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (657/1000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 1
def dCertificate : TensorBernstein3 := [
  ⟨511938576384000000, 0, 0, 0, 1, 0, 0⟩,
  ⟨447457763328000000, 0, 0, 1, 0, 0, 0⟩]
noncomputable def d (p u dummy : ℝ) : ℝ := dPolynomial.eval p u dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p u dummy : ℝ}
    (hp : p∈Icc (13/20) (657/1000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p u dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hu
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, u, dummy] hx
  have he : dReduced.eval p u dummy=d p u dummy-447457763328000000 := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<447457763328000000 := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (657/1000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapZeroRectangle.numerator p u dummy := by
  exact n_pos hp hu hdummy

theorem denominator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (657/1000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapZeroRectangle.denominator p u dummy := by
  exact d_pos hp hu hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0CapZeroRectangleLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0CapZeroTriangleLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-81677420612452142312958852841103555802630147/1050573335467750000000000000)], [(298941237114492319646516308203668197344849357/1050573335467750000000000000)], [(-14402655926376802814230523540072920787899977/42022933418710000000000000)], [(1139309422515697635666629783571137152570659/8404586683742000000000000)]], [[(729995935348161524179679085143745301873907/262643333866937500000000)], [(-5752299510866810358500053344769129303808389/525286667733875000000000)], [(19667360217144877510237247404371120231843/1313216669334687500000)], [(-34409726862768934008450846481015851067029/4202293341871000000000)], [1385813012413852845]], [[(-25872795784469181685099363796613310431/2101146670935500000)], [(520052235806870816734758449491822753043/10505733354677500000)], [(-749800529542616319510651538273143855053/10505733354677500000)], [(88179417001922971638318221966477530833/2101146670935500000)], [-7846075087976520000]], [[19332719318713200000], [(-89135699169847621627973277810124447/1050573335467750)], [(69638596996899431905424148580124447/525286667733875)], [(-87849325884775782435750888650124447/1050573335467750)], [16658333520120000000]], [[-10241621700000000000], [60653788956800000000], [-109332570221600000000], [74639519284800000000], [-15719116320000000000]], [[], [-13905800000000000000], [33373920000000000000], [-25030440000000000000], [5562320000000000000]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-18378708427435069830919845421998250835151/13132166693346875000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(657/1000), (1413/2000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 1050573335467750000000000000
def nCertificate : TensorBernstein3 := [
  ⟨6471617840396759096901449024479720339825869, 0, 5, 0, 4, 0, 0⟩,
  ⟨20275882689062124400410846856562649347049387, 0, 5, 1, 3, 0, 0⟩,
  ⟨22965685934423234798172398352395385141476622, 0, 5, 2, 2, 0, 0⟩,
  ⟨10608667888415997482363489092243566201065184, 0, 5, 3, 1, 0, 0⟩,
  ⟨1470296674194805586473587633759860066812080, 0, 5, 4, 0, 0, 0⟩,
  ⟨33205645668675107395410285144586846288396431, 1, 4, 0, 4, 0, 0⟩,
  ⟨108635528451077329410080954968657454302074168, 1, 4, 1, 3, 0, 0⟩,
  ⟨128248197611173423128490278976754080293608193, 1, 4, 2, 2, 0, 0⟩,
  ⟨62720626834323174847297382171139395534492856, 1, 4, 3, 1, 0, 0⟩,
  ⟨9927098511245524302021448036997798254562400, 1, 4, 4, 0, 0, 0⟩,
  ⟨66218046387206526572180636878026874813548159, 2, 3, 0, 4, 0, 0⟩,
  ⟨224033138864200054784454669594492778873139127, 2, 3, 1, 3, 0, 0⟩,
  ⟨275061612670944966669781654719848313055805952, 2, 3, 2, 2, 0, 0⟩,
  ⟨142593570717160826178162551659569201346343784, 2, 3, 3, 1, 0, 0⟩,
  ⟨25347050523209387720654929656186792350128800, 2, 3, 4, 0, 0, 0⟩,
  ⟨63170301943406005156289164060180587608524581, 3, 2, 0, 4, 0, 0⟩,
  ⟨221031822478852215309238927715826011677509618, 3, 2, 1, 3, 0, 0⟩,
  ⟨283746808622271151465746148722487448720578293, 3, 2, 2, 2, 0, 0⟩,
  ⟨157079357581609677628932170538219212842726056, 3, 2, 3, 1, 0, 0⟩,
  ⟨31194069494784736316135785471377188191132800, 3, 2, 4, 0, 0, 0⟩,
  ⟨28086360669801138317613283037218396730861064, 4, 1, 0, 4, 0, 0⟩,
  ⟨102962980103352793698864485065041082208651592, 4, 1, 1, 3, 0, 0⟩,
  ⟨140370776291251551190913756971812866240788392, 4, 1, 2, 2, 0, 0⟩,
  ⟨84198054951649274555687190897376072779066264, 4, 1, 3, 1, 0, 0⟩,
  ⟨18703898093949378746024635953385892016068400, 4, 1, 4, 0, 0, 0⟩,
  ⟨4400077285323311434995919734957557987314080, 5, 0, 0, 4, 0, 0⟩,
  ⟨17600309141293245739983678939830231949256320, 5, 0, 1, 3, 0, 0⟩,
  ⟨26400463711939868609975518409745347923884480, 5, 0, 2, 2, 0, 0⟩,
  ⟨17600309141293245739983678939830231949256320, 5, 0, 3, 1, 0, 0⟩,
  ⟨4400077285323311434995919734957557987314080, 5, 0, 4, 0, 0, 0⟩]
noncomputable def n (p u dummy : ℝ) : ℝ := nPolynomial.eval p u dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p u dummy : ℝ}
    (hp : p∈Icc (657/1000) (1413/2000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p u dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hu
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, u, dummy] hx
  have he : nReduced.eval p u dummy=n p u dummy-(18378708427435069830919845421998250835151/13132166693346875000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(18378708427435069830919845421998250835151/13132166693346875000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[959396339712000000], [-920317059072000000]], [[], [1302642688000000000]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[-447457763328000000]]]
def dBox : Fin 3→RatInterval := ![⟨(657/1000), (1413/2000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 1
def dCertificate : TensorBernstein3 := [
  ⟨511938576384000000, 0, 1, 0, 1, 0, 0⟩,
  ⟨447457763328000000, 0, 1, 1, 0, 0, 0⟩,
  ⟨511938576384000000, 1, 0, 0, 1, 0, 0⟩,
  ⟨511938576384000000, 1, 0, 1, 0, 0, 0⟩]
noncomputable def d (p u dummy : ℝ) : ℝ := dPolynomial.eval p u dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p u dummy : ℝ}
    (hp : p∈Icc (657/1000) (1413/2000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p u dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hu
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, u, dummy] hx
  have he : dReduced.eval p u dummy=d p u dummy-447457763328000000 := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<447457763328000000 := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (657/1000:ℝ) (1413/2000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapZeroTriangle.numerator p u dummy := by
  exact n_pos hp hu hdummy

theorem denominator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (657/1000:ℝ) (1413/2000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapZeroTriangle.denominator p u dummy := by
  exact d_pos hp hu hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0CapZeroTriangleLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1HeadSquareLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-3748486330224668047419750275730820634649645106860477961/7063707732453334912712256400000000000000000000000000000000)]], [[(-94430698679949000156747878203608615883999309119064519436094733697077017/1382462625092150529141899457170546476034750000000000000000000000000000000)], [(3634350946475149147106993601347777046759136892391990974524714401487873/16921342531127922476696849355767488866665340000000000000000000000000000)], [(-6103259816388429633184340265201146114200478254762302449824155663071/36098864066406234616953278625637309582219392000000000000000000000000)]], [[(324760809709522800054446278115335587941975993111220520911388677457736799769117061/105095907779965740607549800257342108349005387773311750000000000000000000000000000)], [(-187900000190814772625522543303650349567681682757/20133461843948739017218668527700000000000000000)], [(1132485521449609129317700857148503163727356169/128854155801271929710199478577280000000000000)], [(-3152346095875039749952404233859018478091/1288541558012719297101994785772800000000)]], [[(-12591548212426009587545730128321508961958361529/5033365460987184754304667131925000000000000000)], [(2428195105465312610453421387527732078011541/402669236878974780344373370554000000000000)], [(-3152346095875039749952404233859018478091/859027705341812864734663190515200000000)]], [[(10407573791774069520242584992127229/158267997188523801498756937500000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-165753979034846504395128857758427590202466888759512247930279485521323270733912878463/269045523916712295955327488658795797373453792699678080000000000000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 6726138097917807398883187216469894934336344817491952000000000000000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨4143849475871162609878221443960689755061672218987806198256987138033081768347821961575, 0, 4, 0, 3, 0, 0⟩,
  ⟨25745749295294586274062212953208004380352803390571912326605829765724678303969037272225, 0, 4, 1, 2, 0, 0⟩,
  ⟨31919342001371731187426795848914599954575154983166189555551960071754753846895847878475, 0, 4, 2, 1, 0, 0⟩,
  ⟨4356721496976541419081266019911704991925080114934962006975320755179563561274632567825, 0, 4, 3, 0, 0, 0⟩,
  ⟨49145573355350728748102386257113442017212392772744328872388341698428622151146808509832, 1, 3, 0, 3, 0, 0⟩,
  ⟨198983506376948727042478729752225836176827155257339604871391937044042170311232211730496, 1, 3, 1, 2, 0, 0⟩,
  ⟨207999015561554286701306250773441356186315094733188115588559415817453933513579975693996, 1, 3, 2, 1, 0, 0⟩,
  ⟨31897230168019152834131990743282835740244924945212292285659805522667135353494572473332, 1, 3, 3, 0, 0, 0⟩,
  ⟨135820840286633796233503955443173758531441323414796015199250136009378243532687616695342, 2, 2, 0, 3, 0, 0⟩,
  ⟨478486858851822974057779564548195213581185341143885687605391938710599753068284780364026, 2, 2, 1, 2, 0, 0⟩,
  ⟨459695839653746734369987578349934990159220999743137687771491970472438632418167208617026, 2, 2, 2, 1, 0, 0⟩,
  ⟨73756766550707046919508962827696990388351659597468677256387366655798680382570044948342, 2, 2, 3, 0, 0, 0⟩,
  ⟨142887900084258332493610441043804800753386158643488427069191573946730075130446095707488, 3, 1, 0, 3, 0, 0⟩,
  ⟨468753205345480070496137717116946886984587007986585001047221469624249230434109074625464, 3, 1, 1, 2, 0, 0⟩,
  ⟨427731050966328722636261446375026752849312413458547271758239891042943399378537881665964, 3, 1, 2, 1, 0, 0⟩,
  ⟨70268311005330307683075753793567634685791366405845177793061251226572734074874902747988, 3, 1, 3, 0, 0, 0⟩,
  ⟨52203065706731270159078703796137377273763386533506301388650701206438062028557465560403, 4, 0, 0, 3, 0, 0⟩,
  ⟨163906949664192740489018829514830253568879510962639106520349364318039039517087468719709, 4, 0, 1, 2, 0, 0⟩,
  ⟨144517730961646047062397483096679267290834845718603610553489102442276016771054800864459, 4, 0, 2, 1, 0, 0⟩,
  ⟨24186335155293039939365569071595357835427382389711197659936278046952315532524797705153, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(165753979034846504395128857758427590202466888759512247930279485521323270733912878463/269045523916712295955327488658795797373453792699678080000000000000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(165753979034846504395128857758427590202466888759512247930279485521323270733912878463/269045523916712295955327488658795797373453792699678080000000000000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadSquare.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadSquare.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1HeadSquareLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1CapFlatLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-403813685427427769550839292657534994219/2672893893857100776000000000000000000000)], [(83398225653477946888564101069792693/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(55610404367714153863782983065732392317862555330669/10245695027253913855429055761874000000000000000000)], [(-1616006218229522667146268806555914508211056069/100667309219743695086093342638500000000000000)], [(2951253188005627461078870205013762779503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-364218274541313486306844457486796821007693931/100667309219743695086093342638500000000000000)], [(115132739137055113882426638417569026341397/12583413652467961885761667829812500000000)], [(-118273125/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-18645278694670584728791013303434389422483008866566519/11803040671396508761454272237678848000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 23606081342793017522908544475357696000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨166085035485683427111337719168157249469107066933639913, 0, 3, 0, 3, 0, 0⟩,
  ⟨378811509352253802439289630531416772606003754403033489, 0, 3, 1, 2, 0, 0⟩,
  ⟨300980332507636034472605547041483003028737705202526614, 0, 3, 2, 1, 0, 0⟩,
  ⟨37290557389341169457582026606868778844966017733133038, 0, 3, 3, 0, 0, 0⟩,
  ⟨902352619856656444796259383228603228679548340122307771, 1, 2, 0, 3, 0, 0⟩,
  ⟨2164062395489827996604202234382062969146871056726247603, 1, 2, 1, 2, 0, 0⟩,
  ⟨1659719277998440400477718483940827645526101213935847618, 1, 2, 2, 1, 0, 0⟩,
  ⟨234770128202052867856724724961890231859403497331907786, 1, 2, 3, 0, 0, 0⟩,
  ⟨1407941773785645445252502336899336110629834246448392379, 2, 1, 0, 3, 0, 0⟩,
  ⟨3456330530467349462892490394017398977820252821529607347, 2, 1, 1, 2, 0, 0⟩,
  ⟨2619732696808497968697818261232871035077356953822450882, 2, 1, 2, 1, 0, 0⟩,
  ⟨397755095555535458492943215677916924628813378741235914, 2, 1, 3, 0, 0, 0⟩,
  ⟨680245982587374728637392488303922804277499770754881257, 3, 0, 0, 3, 0, 0⟩,
  ⟨1696795023847882171937013236561850799853705911691863441, 3, 0, 1, 2, 0, 0⟩,
  ⟨1286709130835800505902140770728624411154313837574600086, 3, 0, 2, 1, 0, 0⟩,
  ⟨208847317915526061163612332787928144472482696637617902, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(18645278694670584728791013303434389422483008866566519/11803040671396508761454272237678848000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(18645278694670584728791013303434389422483008866566519/11803040671396508761454272237678848000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapFlat.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapFlat.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1CapFlatLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1HeadZeroTriangleLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-314538455133100217790839649216482910741/171065209206854449664000000000000000000000)], [(232046212804321553724540530007092289809/6842608368274177986560000000000000000000)], [(-548008045151278876233367656802272733713/5474086694619342389248000000000000000000)]], [[(11570771949545087759203693451216362272914177/1610676947515899121377493482216000000000000000)], [(-4248148153993927362930499044300882835922435989751/5726851368945419098231087936768000000000000000000)], [(233177300304416922886781561857376801882407630263787/103083324641017543768159582861824000000000000000000)], [(115388936569793/130264268800000)]], [[(-1124333556981553452237298171008013085456901/5592628289985760838116296813250000000000000)], [(229204735990437109374339814045085663992135217/100667309219743695086093342638500000000000000)], [(-903834321608205473325131327666959844891797335101/103083324641017543768159582861824000000000000000)], [(-283047268773/65132134400)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)], [(-95026469809253357657462021473607404193713/50333654609871847543046671319250000000000)], [(2472462410193006332216690989608050306434301/201334618439487390172186685277000000000000)], [(1157184255/162830336)]], [[], [], [(-118273125/20353792)], [(-39424375/10176896)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-25726078931489178581938172768391019495109/8399301772056553478502400000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (1413/2000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 412333298564070175072638331447296000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨3621908070677998217441390206577025513179037563106516, 0, 4, 0, 3, 0, 0⟩,
  ⟨8904256056106784820900831017750229666607528115569648, 0, 4, 1, 2, 0, 0⟩,
  ⟨7333991951586466521896901219379879718545923099921823, 0, 4, 2, 1, 0, 0⟩,
  ⟨1992393273164879749723272087365546227554932547458691, 0, 4, 3, 0, 0, 0⟩,
  ⟨18668746625101335748432650630605139786673677847152464, 1, 3, 0, 3, 0, 0⟩,
  ⟨44087206855492658964215261311133832639501898650941124, 1, 3, 1, 2, 0, 0⟩,
  ⟨34798998393276097718056002142607293535843248172735218, 1, 3, 2, 1, 0, 0⟩,
  ⟨8877528191296616898142662698451102659139402368946558, 1, 3, 3, 0, 0, 0⟩,
  ⟨34888300490671429072080494999713164257853385208074488, 2, 2, 0, 3, 0, 0⟩,
  ⟨78827761531755817589405428476122599243584678519408812, 2, 2, 1, 2, 0, 0⟩,
  ⟨59125785818819254288859515599774081051188431256857727, 2, 2, 2, 1, 0, 0⟩,
  ⟨13627308493241069060149104784619111615825887945523403, 2, 2, 3, 0, 0, 0⟩,
  ⟨28283436647540048041662865737310922087480976831276880, 3, 1, 0, 3, 0, 0⟩,
  ⟨60946852367823047453059225426140591280777613252432076, 3, 1, 1, 2, 0, 0⟩,
  ⟨42775758047383442817383881107305282619815022895197092, 3, 1, 2, 1, 0, 0⟩,
  ⟨8045796364004951472388814005053977399830886474041896, 3, 1, 3, 0, 0, 0⟩,
  ⟨8441974711291956500573631161625872103122231907248340, 4, 0, 0, 3, 0, 0⟩,
  ⟨17302041635453104006968227243401595010087305268394740, 4, 0, 1, 2, 0, 0⟩,
  ⟨11090562196704016703849005305014312196915479211152760, 4, 0, 2, 1, 0, 0⟩,
  ⟨1262928666312614525934997955279916900575405850006360, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p u dummy : ℝ) : ℝ := nPolynomial.eval p u dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p u dummy : ℝ}
    (hp : p∈Icc (13/20) (1413/2000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p u dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hu
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, u, dummy] hx
  have he : nReduced.eval p u dummy=n p u dummy-(25726078931489178581938172768391019495109/8399301772056553478502400000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(25726078931489178581938172768391019495109/8399301772056553478502400000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (1413/2000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p u dummy : ℝ) : ℝ := dPolynomial.eval p u dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p u dummy : ℝ}
    (hp : p∈Icc (13/20) (1413/2000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p u dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hu
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, u, dummy] hx
  have he : dReduced.eval p u dummy=d p u dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (1413/2000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadZeroTriangle.numerator p u dummy := by
  exact n_pos hp hu hdummy

theorem denominator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (1413/2000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadZeroTriangle.denominator p u dummy := by
  exact d_pos hp hu hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1HeadZeroTriangleLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1HeadZeroRectangleLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-423086167986637211308247225244094462619/2672893893857100776000000000000000000000)], [(88324099790017101331352071059967637/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(17750450005981967/3180280000000000)], [(-3214751650358371288308056710407908089150691/191019562086800180429019625500000000000000)], [(3089014552323841708582475383692007825965551/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-572684643121184768113360504327645192099309/191019562086800180429019625500000000000000)], [(104204275423512313887356824997694645533603/12583413652467961885761667829812500000000)], [(-118273125/20353792)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-25726078931489178581938172768391019495109/8399301772056553478502400000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(1413/2000), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 103083324641017543768159582861824000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨2110493677822989125143407790406468025780557976812085, 0, 3, 0, 3, 0, 0⟩,
  ⟨4325510408863276001742056810850398752521826317098685, 0, 3, 1, 2, 0, 0⟩,
  ⟨2772640549176004175962251326253578049228869802788190, 0, 3, 2, 1, 0, 0⟩,
  ⟨315732166578153631483749488819979225143851462501590, 0, 3, 3, 0, 0, 0⟩,
  ⟨8163679687986211782632392608582407429280170767726495, 1, 2, 0, 3, 0, 0⟩,
  ⟨17330613792057255020228142079676240865643188169905975, 1, 2, 1, 2, 0, 0⟩,
  ⟨11316167649403575357523629476015721602714894497304090, 1, 2, 2, 1, 0, 0⟩,
  ⟨1397708881257723555177311097218673058539377095124610, 1, 2, 3, 0, 0, 0⟩,
  ⟨10303831487603400372936577394472505965514498058507423, 2, 1, 0, 3, 0, 0⟩,
  ⟨22503167575930319562837579791311787727952654599491639, 2, 1, 1, 2, 0, 0⟩,
  ⟨14996681078161214232060738517498329330295765147723034, 2, 1, 2, 1, 0, 0⟩,
  ⟨2019970616357368916298156756221621644263858606738818, 2, 1, 3, 0, 0, 0⟩,
  ⟨4265823257505482037420609694809700720765688508577077, 3, 0, 0, 3, 0, 0⟩,
  ⟨9543597532932253510270545878025348091083702469636541, 3, 0, 1, 2, 0, 0⟩,
  ⟨6498687318129556016418411723275588253062150176159326, 3, 0, 2, 1, 0, 0⟩,
  ⟨953171681743103314577612266336061969619136215099862, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (1413/2000) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(25726078931489178581938172768391019495109/8399301772056553478502400000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(25726078931489178581938172768391019495109/8399301772056553478502400000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(1413/2000), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (1413/2000) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (1413/2000:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadZeroRectangle.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (1413/2000:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadZeroRectangle.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1HeadZeroRectangleLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1HeadCapBoundaryTriangleLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-2724276082728054571202714568410065515541/171065209206854449664000000000000000000000)], [(328435717908119727861015526774835594001/6842608368274177986560000000000000000000)], [(-548008045151278876233367656802272733713/5474086694619342389248000000000000000000)]], [[(64211459837332034875726395441959557218389099/8053384737579495606887467411080000000000000000)], [(-8362195764779486225402716813315554950120257874149/17180554106836257294693263810304000000000000000000)], [(206802430840056183276628618459075005389596456553963/103083324641017543768159582861824000000000000000000)], [(115388936569793/130264268800000)]], [[(-872357963938388252258787817194614125846849/16777884869957282514348890439750000000000000)], [(25991961093562292879833321421672453459452769/20133461843948739017218668527700000000000000)], [(-817571461544883348680313851302931074678187609149/103083324641017543768159582861824000000000000000)], [(-283047268773/65132134400)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)], [(-51312614955082157677182767794109880962537/50333654609871847543046671319250000000000)], [(2334701045874792084713085810929805259971949/201334618439487390172186685277000000000000)], [(1157184255/162830336)]], [[], [], [(-118273125/20353792)], [(-39424375/10176896)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-25726078931489178581938172768391019495109/8399301772056553478502400000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (1413/2000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 412333298564070175072638331447296000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨3127279426832058484331854760073233820881260647599316, 0, 4, 0, 3, 0, 0⟩,
  ⟨8186825524960313343285545759481413474234149135217648, 0, 4, 1, 2, 0, 0⟩,
  ⟨7111190064285934777391151407614855218470321035077023, 0, 4, 2, 1, 0, 0⟩,
  ⟨1992393273164879749723272087365546227554932547458691, 0, 4, 3, 0, 0, 0⟩,
  ⟨15782153363046323366549066165960219786059046555811664, 1, 3, 0, 3, 0, 0⟩,
  ⟨40222784557182072967656778959701277335377120830551748, 1, 3, 1, 2, 0, 0⟩,
  ⟨33821169357020524103381104255819658232333101643686642, 1, 3, 2, 1, 0, 0⟩,
  ⟨8877528191296616898142662698451102659139402368946558, 1, 3, 3, 0, 0, 0⟩,
  ⟨28919578686536032049796680388212414509512378034960632, 2, 2, 0, 3, 0, 0⟩,
  ⟨71640419942664042587262807693868110298706015017101484, 2, 2, 1, 2, 0, 0⟩,
  ⟨57907166033862876309000709429020341854650774927664255, 2, 2, 2, 1, 0, 0⟩,
  ⟨13627308493241069060149104784619111615825887945523403, 2, 2, 3, 0, 0, 0⟩,
  ⟨23013556387440761236951926054853338381325569288724304, 3, 1, 0, 3, 0, 0⟩,
  ⟨55319196752344236127344979354886481407806924379259084, 3, 1, 1, 2, 0, 0⟩,
  ⟨42417982692003918296380574718508756452999741564576676, 3, 1, 2, 1, 0, 0⟩,
  ⟨8045796364004951472388814005053977399830886474041896, 3, 1, 3, 0, 0, 0⟩,
  ⟨6748851637118994069372457072527909836990977161976020, 4, 0, 0, 3, 0, 0⟩,
  ⟨15714735841901953164453404861238234970243881057491700, 4, 0, 1, 2, 0, 0⟩,
  ⟨11196379477325828292535357011948914423203309745522040, 4, 0, 2, 1, 0, 0⟩,
  ⟨1262928666312614525934997955279916900575405850006360, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p u dummy : ℝ) : ℝ := nPolynomial.eval p u dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p u dummy : ℝ}
    (hp : p∈Icc (13/20) (1413/2000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p u dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hu
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, u, dummy] hx
  have he : nReduced.eval p u dummy=n p u dummy-(25726078931489178581938172768391019495109/8399301772056553478502400000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(25726078931489178581938172768391019495109/8399301772056553478502400000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (1413/2000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p u dummy : ℝ) : ℝ := dPolynomial.eval p u dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p u dummy : ℝ}
    (hp : p∈Icc (13/20) (1413/2000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p u dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hu
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, u, dummy] hx
  have he : dReduced.eval p u dummy=d p u dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (1413/2000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadCapBoundaryTriangle.numerator p u dummy := by
  exact n_pos hp hu hdummy

theorem denominator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (1413/2000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadCapBoundaryTriangle.denominator p u dummy := by
  exact d_pos hp hu hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1HeadCapBoundaryTriangleLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1HeadCapBoundaryRectangleLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-406861570049411371362314349088955740819/2672893893857100776000000000000000000000)], [(83398225653477946888564101069792693/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(36460099355572492531999421490692967/6682234734642751940000000000000000)], [(-5830920832885289147953519563056796636689/362465962214042088100606500000000000000)], [(2951253188005627461078870205013762779503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-1308110412227842033545330302362422113311/362465962214042088100606500000000000000)], [(115132739137055113882426638417569026341397/12583413652467961885761667829812500000000)], [(-118273125/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-25726078931489178581938172768391019495109/8399301772056553478502400000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(1413/2000), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 103083324641017543768159582861824000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨1687212909279748517343114268131977459247744290494005, 0, 3, 0, 3, 0, 0⟩,
  ⟨3928683960475488291113351215309558742560970264372925, 0, 3, 1, 2, 0, 0⟩,
  ⟨2799094869331457073133839252987228605800827436380510, 0, 3, 2, 1, 0, 0⟩,
  ⟨315732166578153631483749488819979225143851462501590, 0, 3, 3, 0, 0, 0⟩,
  ⟨6391858582521363850970102179449037346686571905190303, 1, 2, 0, 3, 0, 0⟩,
  ⟨15205261932358267053488907187176112964334831114232119, 1, 2, 1, 2, 0, 0⟩,
  ⟨10983661118029821572304104891263601857907323686652954, 1, 2, 2, 1, 0, 0⟩,
  ⟨1418733104118109805034730975833311132446564477611138, 1, 2, 3, 0, 0, 0⟩,
  ⟨7888152779933899146753994804281913462410520954166431, 2, 1, 0, 3, 0, 0⟩,
  ⟨19065787236151462336764276787571512130715565630645303, 2, 1, 1, 2, 0, 0⟩,
  ⟨13923629530967440679921672453310030634504525908960538, 2, 1, 2, 1, 0, 0⟩,
  ⟨1968620701272951364049811105583006042605731232481666, 2, 1, 3, 0, 0, 0⟩,
  ⟨3190511253855486740737372824700075653884890098486069, 3, 0, 0, 3, 0, 0⟩,
  ⟨7810221705758292357219818610910624145681295057833917, 3, 0, 1, 2, 0, 0⟩,
  ⟨5760075723758684963582504610239323619137619935735902, 3, 0, 2, 1, 0, 0⟩,
  ⟨872623910896198118109195550304896214216214976388054, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (1413/2000) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(25726078931489178581938172768391019495109/8399301772056553478502400000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(25726078931489178581938172768391019495109/8399301772056553478502400000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(1413/2000), (391/500)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (1413/2000) (391/500))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (1413/2000:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadCapBoundaryRectangle.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (1413/2000:ℝ) (391/500))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadCapBoundaryRectangle.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1HeadCapBoundaryRectangleLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1CapZeroRectangleLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-68574834745046884706067626951857290116126397/1050573335467750000000000000)], [(18177772536641617118628477270391491259917861/1050573335467750000000000000)], [(-62925482657779097851595017959116568205383/42022933418710000000000000)], [(355499999132356691840808330939353607003/8404586683742000000000000)]], [[(608081628128695810166932936922205779170157/262643333866937500000000)], [(-3333477627886298155820166041552299568103/5252866677338750000000)], [(126769173334810489046694011514642662697/2101146670935500000000)], [(-23369506433893719/10)], [30296717857395]], [[(-22250599795990608494982888802767118881/2101146670935500000)], [(4466965093609602243184906082537097603/2101146670935500000)], [-136030022983265400], [2754247077945000]], [[17116820871853200000], [-2254252256031600000], [74188473480000000]], [[-9291536700000000000], [624482100000000000]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-20215628116915719569502967626462143326401/13132166693346875000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(13/20), (657/1000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 1050573335467750000000000000
def nCertificate : TensorBernstein3 := [
  ⟨6340127366304714155108787938706900648919723, 0, 4, 0, 4, 0, 0⟩,
  ⟨20561469932251591016594717646882018635956753, 0, 4, 1, 3, 0, 0⟩,
  ⟨24295610939973761398410489717560603185742346, 0, 4, 2, 2, 0, 0⟩,
  ⟨11938439360228871208290091315998922260168700, 0, 4, 3, 1, 0, 0⟩,
  ⟨1884859786758546397436610288925937061463384, 0, 4, 4, 0, 0, 0⟩,
  ⟨25635482423921790770409606012808973503893288, 1, 3, 0, 4, 0, 0⟩,
  ⟨83036037058012653480503821801574132874990396, 1, 3, 1, 3, 0, 0⟩,
  ⟨97737819998397225780357850923058611606612660, 1, 3, 2, 2, 0, 0⟩,
  ⟨47603075000195318768759509444096820407328784, 1, 3, 3, 1, 0, 0⟩,
  ⟨7348787640582726784445571089632118171813232, 1, 3, 4, 0, 0, 0⟩,
  ⟨38826251565262028388433607247882722205577026, 2, 2, 0, 4, 0, 0⟩,
  ⟨125546212224409337887921512399246268050166170, 2, 2, 1, 3, 0, 0⟩,
  ⟨147097589981089887773266888301425275903697404, 2, 2, 2, 2, 0, 0⟩,
  ⟨70915833907739709665496233755777676684456652, 2, 2, 3, 1, 0, 0⟩,
  ⟨10663005796539086293139867051327196625348392, 2, 2, 4, 0, 0, 0⟩,
  ⟨26104028060288425662652365744831026495153080, 3, 1, 0, 4, 0, 0⟩,
  ⟨84219816714864410026205769297109112019188164, 3, 1, 1, 3, 0, 0⟩,
  ⟨98148285175818016956615090157970429730526212, 3, 1, 2, 2, 0, 0⟩,
  ⟨46765422965690240602729371534594081187601752, 3, 1, 3, 1, 0, 0⟩,
  ⟨6816350054077043458948143409887986981110624, 3, 1, 4, 0, 0, 0⟩,
  ⟨6573108115424347090953666359625377144549619, 4, 0, 0, 4, 0, 0⟩,
  ⟨21148079442549874219238630669129958208055637, 4, 0, 1, 3, 0, 0⟩,
  ⟨24492768355467573207826833180318162247699122, 4, 0, 2, 2, 0, 0⟩,
  ⟨11514135674671211737365646448039302650305184, 4, 0, 3, 1, 0, 0⟩,
  ⟨1617250249353257565560237410116971466112080, 4, 0, 4, 0, 0, 0⟩]
noncomputable def n (p u dummy : ℝ) : ℝ := nPolynomial.eval p u dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p u dummy : ℝ}
    (hp : p∈Icc (13/20) (657/1000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p u dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hu
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, u, dummy] hx
  have he : nReduced.eval p u dummy=n p u dummy-(20215628116915719569502967626462143326401/13132166693346875000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(20215628116915719569502967626462143326401/13132166693346875000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[959396339712000000], [-64480813056000000]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[-447457763328000000]]]
def dBox : Fin 3→RatInterval := ![⟨(13/20), (657/1000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 1
def dCertificate : TensorBernstein3 := [
  ⟨511938576384000000, 0, 0, 0, 1, 0, 0⟩,
  ⟨447457763328000000, 0, 0, 1, 0, 0, 0⟩]
noncomputable def d (p u dummy : ℝ) : ℝ := dPolynomial.eval p u dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p u dummy : ℝ}
    (hp : p∈Icc (13/20) (657/1000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p u dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hu
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, u, dummy] hx
  have he : dReduced.eval p u dummy=d p u dummy-447457763328000000 := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<447457763328000000 := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (657/1000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapZeroRectangle.numerator p u dummy := by
  exact n_pos hp hu hdummy

theorem denominator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (657/1000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapZeroRectangle.denominator p u dummy := by
  exact d_pos hp hu hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1CapZeroRectangleLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1CapZeroTriangleLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-68574834745046884706067626951857290116126397/1050573335467750000000000000)], [(259446389841157626147697357404678557073373107/1050573335467750000000000000)], [(-12818596876294189941685666096481523055326327/42022933418710000000000000)], [(1033619051947643302222315006945069833407709/8404586683742000000000000)]], [[(608081628128695810166932936922205779170157/262643333866937500000000)], [(-4941395569262379257939575140825569901342139/525286667733875000000000)], [(17274139311996072872559532697621730473493/1313216669334687500000)], [(-30747853067625138757718302454367226185579/4202293341871000000000)], [1257255231774560595]], [[(-22250599795990608494982888802767118881/2101146670935500000)], [(453464837352495277488707329690240331693/10505733354677500000)], [(-663065951946393619496991407850510633203/10505733354677500000)], [(79001852402988258779427316488421179183/2101146670935500000)], [-7118217872750520000]], [[17116820871853200000], [(-78922350251587985860600823174112097/1050573335467750)], [(62079194762166224678543319444112097/525286667733875)], [(-78993914826382217492138420014112097/1050573335467750)], [15112989114120000000]], [[-9291536700000000000], [54453512316800000000], [-98299494341600000000], [67398419044800000000], [-14260900320000000000]], [[], [-12615800000000000000], [30277920000000000000], [-22708440000000000000], [5046320000000000000]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-20215628116915719569502967626462143326401/13132166693346875000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(657/1000), (1413/2000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def nScale : ℚ := 1050573335467750000000000000
def nCertificate : TensorBernstein3 := [
  ⟨6573108115424347090953666359625377144549619, 0, 5, 0, 4, 0, 0⟩,
  ⟨21148079442549874219238630669129958208055637, 0, 5, 1, 3, 0, 0⟩,
  ⟨24492768355467573207826833180318162247699122, 0, 5, 2, 2, 0, 0⟩,
  ⟨11514135674671211737365646448039302650305184, 0, 5, 3, 1, 0, 0⟩,
  ⟨1617250249353257565560237410116971466112080, 0, 5, 4, 0, 0, 0⟩,
  ⟨34197828844227971698701736774796723309997681, 1, 4, 0, 4, 0, 0⟩,
  ⟨113518864837480713685349658440854295731164168, 1, 4, 1, 3, 0, 0⟩,
  ⟨135669403133993435966520106817410054707746943, 1, 4, 2, 2, 0, 0⟩,
  ⟨67001011886453714770855545792339916363742856, 1, 4, 3, 1, 0, 0⟩,
  ⟨10675131880471804554782156488685559077162400, 1, 4, 4, 0, 0, 0⟩,
  ⟨68700797335508801123492623224166880275409409, 2, 3, 0, 4, 0, 0⟩,
  ⟨234050493401885514669642127219136317496890377, 2, 3, 1, 3, 0, 0⟩,
  ⟨289110968220730054836024874059233321614205952, 2, 3, 2, 2, 0, 0⟩,
  ⟨150627815394953680992818525148960606040253784, 2, 3, 3, 1, 0, 0⟩,
  ⟨26866543240600339702943155084696721647528800, 2, 3, 4, 0, 0, 0⟩,
  ⟨65716154300427167878997124349331034911738331, 3, 2, 0, 4, 0, 0⟩,
  ⟨230521041180704568237297452423374685983367118, 3, 2, 1, 3, 0, 0⟩,
  ⟨296627319991530074135489246196857792372252043, 3, 2, 2, 2, 0, 0⟩,
  ⟨164556133642655115075074632520915666441356056, 3, 2, 3, 1, 0, 0⟩,
  ⟨32733700531402441297885714398101525140732800, 3, 2, 4, 0, 0, 0⟩,
  ⟨29197086387926136657357495594632374014491064, 4, 1, 0, 4, 0, 0⟩,
  ⟨107073306779903203850341889230167386360441592, 4, 1, 1, 3, 0, 0⟩,
  ⟨146037402012152791606880694122707914994378392, 4, 1, 2, 2, 0, 0⟩,
  ⟨87643229236300518292165702933443166965396264, 4, 1, 3, 1, 0, 0⟩,
  ⟨19482047616124793878269402446270264316968400, 4, 1, 4, 0, 0, 0⟩,
  ⟨4557008694204145294104924054296873212714080, 5, 0, 0, 4, 0, 0⟩,
  ⟨18228034776816581176419696217187492850856320, 5, 0, 1, 3, 0, 0⟩,
  ⟨27342052165224871764629544325781239276284480, 5, 0, 2, 2, 0, 0⟩,
  ⟨18228034776816581176419696217187492850856320, 5, 0, 3, 1, 0, 0⟩,
  ⟨4557008694204145294104924054296873212714080, 5, 0, 4, 0, 0, 0⟩]
noncomputable def n (p u dummy : ℝ) : ℝ := nPolynomial.eval p u dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p u dummy : ℝ}
    (hp : p∈Icc (657/1000) (1413/2000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<n p u dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hu
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, u, dummy] hx
  have he : nReduced.eval p u dummy=n p u dummy-(20215628116915719569502967626462143326401/13132166693346875000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(20215628116915719569502967626462143326401/13132166693346875000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[959396339712000000], [-920317059072000000]], [[], [1302642688000000000]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[-447457763328000000]]]
def dBox : Fin 3→RatInterval := ![⟨(657/1000), (1413/2000)⟩, ⟨0, 1⟩, ⟨0, 1⟩]
def dScale : ℚ := 1
def dCertificate : TensorBernstein3 := [
  ⟨511938576384000000, 0, 1, 0, 1, 0, 0⟩,
  ⟨447457763328000000, 0, 1, 1, 0, 0, 0⟩,
  ⟨511938576384000000, 1, 0, 0, 1, 0, 0⟩,
  ⟨511938576384000000, 1, 0, 1, 0, 0, 0⟩]
noncomputable def d (p u dummy : ℝ) : ℝ := dPolynomial.eval p u dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p u dummy : ℝ}
    (hp : p∈Icc (657/1000) (1413/2000))
    (hu : u∈Icc 0 1)
    (hdummy : dummy∈Icc 0 1)
    : 0<d p u dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, u, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hu
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, u, dummy] hx
  have he : dReduced.eval p u dummy=d p u dummy-447457763328000000 := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p u dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<447457763328000000 := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (657/1000:ℝ) (1413/2000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapZeroTriangle.numerator p u dummy := by
  exact n_pos hp hu hdummy

theorem denominator_pos {p u dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (657/1000:ℝ) (1413/2000))
    (hu : u∈Icc (0:ℝ) (1))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapZeroTriangle.denominator p u dummy := by
  exact d_pos hp hu hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1CapZeroTriangleLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper0HeadSquareLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-3748486330224668047419750275730820634649645106860477961/7063707732453334912712256400000000000000000000000000000000)]], [[(-5923048648355923937072301846803874876316751286037044624198543907679209117/70505593879699676986236872315697870277772250000000000000000000000000000000)], [(2096293009122325873347389227381545925482744735474578478763662799294799/8460671265563961238348424677883744433332670000000000000000000000000000)], [(-6727334798802630415283596669242861937796177056950302430822044089121/36098864066406234616953278625637309582219392000000000000000000000000)]], [[(387716622131186393710304217619889899120778187090311808683466171371768049769117061/105095907779965740607549800257342108349005387773311750000000000000000000000000000)], [(-108918545378128011172874967129245092362828926591/10066730921974369508609334263850000000000000000)], [(1279128737326491306774274353111849802826856119/128854155801271929710199478577280000000000000)], [(-3474682092298477128274714468776989105141/1288541558012719297101994785772800000000)]], [[(-14306980093391990385304774909775583892790080279/5033365460987184754304667131925000000000000000)], [(1358262327133038672681363946330928401953883/201334618439487390172186685277000000000000)], [(-3474682092298477128274714468776989105141/859027705341812864734663190515200000000)]], [[(10407573791774069520242584992127229/158267997188523801498756937500000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-201613904339705003887121566277454120597026561391373824871068694796732493867211850123/98913795557614814689458635536321984328475659080764000000000000000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 3363069048958903699441593608234947467168172408745976000000000000000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨22127833522648015737426855344773676982025701288048746726560177336028549439875495700557, 0, 4, 0, 3, 0, 0⟩,
  ⟨66130434795278172002173174892900848664920754962174133936697898975918455598307913158421, 0, 4, 1, 2, 0, 0⟩,
  ⟨55612323267485724628387066517338145864281929798111386465110245375472329074917620362046, 0, 4, 2, 1, 0, 0⟩,
  ⟨6854872747549970132162133253433440100298903087306710045616335623088904791485202904182, 0, 4, 3, 0, 0, 0⟩,
  ⟨97966340149304757457050475780954898021706877312489324697631023812307659595551990613011, 1, 3, 0, 3, 0, 0⟩,
  ⟨291346507161421034270856836578129837530200423090956722603309215868335793243392538201783, 1, 3, 1, 2, 0, 0⟩,
  ⟨244098214807938475391037862297798562315357919489074707662329096965051782279628386036408, 1, 3, 2, 1, 0, 0⟩,
  ⟨31236542695608468738794828424726923067982192624264032740311740315124374881787838447636, 1, 3, 3, 0, 0, 0⟩,
  ⟨161966828498723358848181345362064709182496956460045312119380142997142722901464358790379, 2, 2, 0, 3, 0, 0⟩,
  ⟨479567213058857236852806029433712004482913263127740535747605726681936425431214219118887, 2, 2, 1, 2, 0, 0⟩,
  ⟨400445818718686541029748103029470014852161258924285941510747246942973316445213519401012, 2, 2, 2, 1, 0, 0⟩,
  ⟨52918786651068802794672393858502499112066048381507598709335193508559808290463659072504, 2, 2, 3, 0, 0, 0⟩,
  ⟨118577230596448830424517524558091793089914467425494257476902865474596284775014728543953, 3, 1, 0, 3, 0, 0⟩,
  ⟨349704598367892149343039521992676450505389393832349464627278249913248990133202476266109, 3, 1, 1, 2, 0, 0⟩,
  ⟨291121678706778012771337299517999767144787449402170080982785393489011279693932362140984, 3, 1, 2, 1, 0, 0⟩,
  ⟨39566134231785769981308816249354631742249366357461309697629810882842711835744614418828, 3, 1, 3, 0, 0, 0⟩,
  ⟨32449369857764597170226836787951649709912048434583893440107959394812465693226864666028, 4, 0, 0, 3, 0, 0⟩,
  ⟨95354841075324926381718265711423469176195883167474627880827011446969283339072882190584, 4, 0, 1, 2, 0, 0⟩,
  ⟨79163134928691374127041103736220203032142264502930571003800169458856797445429608414334, 4, 0, 2, 1, 0, 0⟩,
  ⟨11029478662157849667536154717888960360679968957605403794504412507398167299583590889778, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(201613904339705003887121566277454120597026561391373824871068694796732493867211850123/98913795557614814689458635536321984328475659080764000000000000000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(201613904339705003887121566277454120597026561391373824871068694796732493867211850123/98913795557614814689458635536321984328475659080764000000000000000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadSquare.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadSquare.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper0HeadSquareLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper0CapFlatLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-470272463196815730653662341750276712969/2672893893857100776000000000000000000000)], [(47284303827534513663328459687070859/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(65329043794025186891366123589499445919425055330669/10245695027253913855429055761874000000000000000000)], [(-1853030922623433331961472448582379363679806069/100667309219743695086093342638500000000000000)], [(3314077199103694962452914920959907799034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-418545495632493530650371668937675727257693931/100667309219743695086093342638500000000000000)], [(129400413613291329286209694977407893528897/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-704899669189894134862875526875053711864395860504341/138859302016429514840638496913868800000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 23606081342793017522908544475357696000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨609205702577009465603907523873586463202659001461807575, 0, 3, 0, 3, 0, 0⟩,
  ⟨1428214652539539211314104700196196903677157466685554895, 0, 3, 1, 2, 0, 0⟩,
  ⟨1006424063713745305653417868900345540065820761509485290, 0, 3, 2, 1, 0, 0⟩,
  ⟨119832943762282002926688839568759131016947296285737970, 0, 3, 3, 0, 0, 0⟩,
  ⟨2008742007258213024167505895521611891383666568787070853, 1, 2, 0, 3, 0, 0⟩,
  ⟨4755022164057849910553082855047158604884439496380508269, 1, 2, 1, 2, 0, 0⟩,
  ⟨3378071690870182692688641303186559817325540263606117054, 1, 2, 2, 1, 0, 0⟩,
  ⟨425760980037786727112000484871500688119767336012679638, 1, 2, 3, 0, 0, 0⟩,
  ⟨2200324864266057870384994680109802315562497518995870085, 2, 1, 0, 3, 0, 0⟩,
  ⟨5253777500787484731705363934912111218118641766417870445, 2, 1, 1, 2, 0, 0⟩,
  ⟨3760281152298378856030056288565287980017539432689362110, 2, 1, 2, 1, 0, 0⟩,
  ⟨497513917678234507377154875210882151774520185267361750, 2, 1, 3, 0, 0, 0⟩,
  ⟨800993063054021065734625846411086300740749748412193751, 3, 0, 0, 3, 0, 0⟩,
  ⟨1927583499676674294206074393909077756989139126947677903, 3, 0, 1, 2, 0, 0⟩,
  ⟨1389247035549441730734521468127001942835599320817491178, 3, 0, 2, 1, 0, 0⟩,
  ⟨191790384871896537105072767857450008030959942282007026, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(704899669189894134862875526875053711864395860504341/138859302016429514840638496913868800000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(704899669189894134862875526875053711864395860504341/138859302016429514840638496913868800000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0CapFlat.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0CapFlat.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper0CapFlatLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper0HeadZeroLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-489544945756025172411070274336836181369/2672893893857100776000000000000000000000)], [(49747240895804090884722444682158331/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(20767131110825717/3180280000000000)], [(-3664513897785146743365369124120365120400691/191019562086800180429019625500000000000000)], [(3451838563421909209956520099638152845496801/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-675772349176554871232007964386238942099309/191019562086800180429019625500000000000000)], [(118471949899748529291139881557533512721103/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-18244733719834614428476442439857100713920501950389/3031862489441692463769399495936000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 103083324641017543768159582861824000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨4011462016310462142683853802384381364855197093671691, 0, 3, 0, 3, 0, 0⟩,
  ⟨8538332450057904867446943514833910228801895748382883, 0, 3, 1, 2, 0, 0⟩,
  ⟨5442310026461704143787759729242993295094995721024418, 0, 3, 2, 1, 0, 0⟩,
  ⟨620320946474376890568199042955141424273297066313226, 0, 3, 3, 0, 0, 0⟩,
  ⟨13284904647297167752849073634718364258607231198293281, 1, 2, 0, 3, 0, 0⟩,
  ⟨28698962743555470288668474051282040264522739652537833, 1, 2, 1, 2, 0, 0⟩,
  ⟨18599013357793474353723463668080406538921093712327398, 1, 2, 2, 1, 0, 0⟩,
  ⟨2285258519034040467724745090863837888005585258082846, 1, 2, 3, 0, 0, 0⟩,
  ⟨14624601445736057793239191348087910415157769201582369, 2, 1, 0, 3, 0, 0⟩,
  ⟨32025095353672634688904949000806204381993949128911337, 2, 1, 1, 2, 0, 0⟩,
  ⟨21079291987184440898237551433023810119113820141517542, 2, 1, 2, 1, 0, 0⟩,
  ⟨2764760532965254887582570380514699882902640214188574, 2, 1, 3, 0, 0, 0⟩,
  ⟨5353093980594566660434360078535222282926242534770443, 3, 0, 0, 3, 0, 0⟩,
  ⟨11870270557710712699764584152701958630834627538185379, 3, 0, 1, 2, 0, 0⟩,
  ⟨7928394153388314120383013182530281159849244463643554, 3, 0, 2, 1, 0, 0⟩,
  ⟨1101758126250805787786412895387298180690859460228618, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(18244733719834614428476442439857100713920501950389/3031862489441692463769399495936000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(18244733719834614428476442439857100713920501950389/3031862489441692463769399495936000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadZero.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadZero.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper0HeadZeroLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper0HeadCapBoundaryLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-473320347818799332465137398181697459569/2672893893857100776000000000000000000000)], [(47284303827534513663328459687070859/106915755754284031040000000000000000)], [(-403845458779687876443982250124447/1368521673654835597312000000000000)]], [[(42798588816288963888393249615692967/6682234734642751940000000000000000)], [(-6684359632556589821686560196287265386689/362465962214042088100606500000000000000)], [(3314077199103694962452914920959907799034449/201334618439487390172186685277000000000000)], [(-43455625/10176896)]], [[(-1503722757683952286142384306268672113311/362465962214042088100606500000000000000)], [(129400413613291329286209694977407893528897/12583413652467961885761667829812500000000)], [(-130366875/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-17060207677968361539235020145281133722701071969333/3031862489441692463769399495936000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 103083324641017543768159582861824000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨2976423898083919444234825290290339175675859302936587, 0, 3, 0, 3, 0, 0⟩,
  ⟨6925778279154301509098841321765934916503870194647971, 0, 3, 1, 2, 0, 0⟩,
  ⟨4824520088361190885654477690253477294274847338668706, 0, 3, 2, 1, 0, 0⟩,
  ⟨580047061050924292333990684939558546571836446957322, 0, 3, 3, 0, 0, 0⟩,
  ⟨9771978669774381813436413730684519247275047113698337, 1, 2, 0, 3, 0, 0⟩,
  ⟨22974089748907772838034798011032444697418529691606761, 1, 2, 1, 2, 0, 0⟩,
  ⟨16170467875082452393336744697509490088416551130355686, 1, 2, 2, 1, 0, 0⟩,
  ⟨2068660053447930018559042256508671993273068552447262, 1, 2, 3, 0, 0, 0⟩,
  ⟨10661711103235382989658885942490136786788400573155361, 2, 1, 0, 3, 0, 0⟩,
  ⟨25298834823898874182652517660098763771995638752023273, 2, 1, 1, 2, 0, 0⟩,
  ⟨17973674956089778452111401331462804914926287386507238, 2, 1, 2, 1, 0, 0⟩,
  ⟨2422513689143678144128546214063361660344049207639326, 2, 1, 3, 0, 0, 0⟩,
  ⟨3867049359794557100427732165630058956932705324583947, 3, 0, 0, 3, 0, 0⟩,
  ⟨9253202438894312293627864961434560716311456941635491, 3, 0, 1, 2, 0, 0⟩,
  ⟨6630406254117426384340438314809098846015061281391266, 3, 0, 2, 1, 0, 0⟩,
  ⟨934793724996308897873929306028350455386309664339722, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(17060207677968361539235020145281133722701071969333/3031862489441692463769399495936000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(17060207677968361539235020145281133722701071969333/3031862489441692463769399495936000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadCapBoundary.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadCapBoundary.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper0HeadCapBoundaryLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper1HeadSquareLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-3748486330224668047419750275730820634649645106860477961/7063707732453334912712256400000000000000000000000000000000)]], [[(-94430698679949000156747878203608615883999309119064519436094733697077017/1382462625092150529141899457170546476034750000000000000000000000000000000)], [(3634350946475149147106993601347777046759136892391990974524714401487873/16921342531127922476696849355767488866665340000000000000000000000000000)], [(-6103259816388429633184340265201146114200478254762302449824155663071/36098864066406234616953278625637309582219392000000000000000000000000)]], [[(324760809709522800054446278115335587941975993111220520911388677457736799769117061/105095907779965740607549800257342108349005387773311750000000000000000000000000000)], [(-187900000190814772625522543303650349567681682757/20133461843948739017218668527700000000000000000)], [(1132485521449609129317700857148503163727356169/128854155801271929710199478577280000000000000)], [(-3152346095875039749952404233859018478091/1288541558012719297101994785772800000000)]], [[(-12591548212426009587545730128321508961958361529/5033365460987184754304667131925000000000000000)], [(2428195105465312610453421387527732078011541/402669236878974780344373370554000000000000)], [(-3152346095875039749952404233859018478091/859027705341812864734663190515200000000)]], [[(10407573791774069520242584992127229/158267997188523801498756937500000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-12253540065382440548980878250673030964744400782309257724132035114613061116294385669/5818458562212636158203449149195410842851509357692000000000000000000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 3363069048958903699441593608234947467168172408745976000000000000000000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨21090911433510165747167514991160021616790265724072302828905527875989222573234488844307, 0, 4, 0, 3, 0, 0⟩,
  ⟨66921610572529962247393904036689125724165472853277009663915213977330094435411002552171, 0, 4, 1, 2, 0, 0⟩,
  ⟨57227001221256615534083230827613632585143140231259261680485083039448583062394668624546, 0, 4, 2, 1, 0, 0⟩,
  ⟨7082546157791050637310947628889011897622263652174750964548316296246349325218154916682, 0, 4, 3, 0, 0, 0⟩,
  ⟨93852758553060876736483568363686673273916217156290717309734334130482809131512891469261, 1, 3, 0, 3, 0, 0⟩,
  ⟨294585057994017780336081785979370960612780752635952410440883157161670617325360489033033, 1, 3, 1, 2, 0, 0⟩,
  ⟨250547835072335960974615053872743287991834018643987624287535891671408367752669167786408, 1, 3, 2, 1, 0, 0⟩,
  ⟨32141272227383863075102456631945912260659093244358039040670487596072473308821570222636, 1, 3, 3, 0, 0, 0⟩,
  ⟨155857110073847411382354624864827471249210064834885768814678494838017880396693102496629, 2, 2, 0, 3, 0, 0⟩,
  ⟨484532269916592880332279093944489528173869760463189145080949092279472189161999535250137, 2, 2, 1, 2, 0, 0⟩,
  ⟨410088531312493201476651483464712881488474907950991489009058080729670025579473575076012, 2, 2, 2, 1, 0, 0⟩,
  ⟨54262930673467411804774732427306283651181554747627805902110509286917442439167142322504, 2, 2, 3, 0, 0, 0⟩,
  ⟨114551138122530224252730525787224299809648409072920669646115072811252537441025485962703, 3, 1, 0, 3, 0, 0⟩,
  ⟨353083585404384042404128479455573903984870293458489885945360215771414243447281613609859, 3, 1, 1, 2, 0, 0⟩,
  ⟨297516361440754814634974326984637985372249092312921238619879361279093705493238321290984, 3, 1, 2, 1, 0, 0⟩,
  ⟨40450799080542864353231371663356498228108384737615869462721690881334261986982193643828, 3, 1, 3, 0, 0, 0⟩,
  ⟨31456336301615907733958991450666824980377657114947685423779774668808037266610786091028, 4, 0, 0, 3, 0, 0⟩,
  ⟨96216146309426131783338378920996244988055897112059251975922237999521958167231564840584, 4, 0, 1, 2, 0, 0⟩,
  ⟨80750047379488110221655778032284793578905147108741222552415260504622845596039245376834, 4, 0, 2, 1, 0, 0⟩,
  ⟨11247055610050648860515185394850459702777021026865721748247743335322737195418466627278, 4, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(12253540065382440548980878250673030964744400782309257724132035114613061116294385669/5818458562212636158203449149195410842851509357692000000000000000000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(12253540065382440548980878250673030964744400782309257724132035114613061116294385669/5818458562212636158203449149195410842851509357692000000000000000000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadSquare.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadSquare.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper1HeadSquareLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper1CapFlatLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-403813685427427769550839292657534994219/2672893893857100776000000000000000000000)], [(83398225653477946888564101069792693/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(55610404367714153863782983065732392317862555330669/10245695027253913855429055761874000000000000000000)], [(-1616006218229522667146268806555914508211056069/100667309219743695086093342638500000000000000)], [(2951253188005627461078870205013762779503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-364218274541313486306844457486796821007693931/100667309219743695086093342638500000000000000)], [(115132739137055113882426638417569026341397/12583413652467961885761667829812500000000)], [(-118273125/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-723934927367256560650571645278814480345437395208091/138859302016429514840638496913868800000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 23606081342793017522908544475357696000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨594467602324282282784377335213393121463741431302638825, 0, 3, 0, 3, 0, 0⟩,
  ⟨1439459883058604834377967777290261751412430893335136145, 0, 3, 1, 2, 0, 0⟩,
  ⟨1029373990046523168343095311457035362713038819217872790, 0, 3, 2, 1, 0, 0⟩,
  ⟨123068937652433615310597179697398461658724357185375470, 0, 3, 3, 0, 0, 0⟩,
  ⟨1965571402511530122179402118249818966540476358309564603, 1, 2, 0, 3, 0, 0⟩,
  ⟨4788789289788687897155909953047980936253602276329252019, 1, 2, 1, 2, 0, 0⟩,
  ⟨3445205291628647799440853767221212781613754436731279554, 1, 2, 2, 1, 0, 0⟩,
  ⟨435069696375934357673609446229036031445628518711592138, 1, 2, 3, 0, 0, 0⟩,
  ⟨2158282177627151824888463556602652666649119808518363835, 2, 1, 0, 3, 0, 0⟩,
  ⟨5287524204185229332218670540553883479178397046366614195, 2, 1, 1, 2, 0, 0⟩,
  ⟨3825524986156494091801147505211724922744313605814524610, 2, 1, 2, 1, 0, 0⟩,
  ⟨506385858626606255206190617920769362621911367966274250, 2, 1, 3, 0, 0, 0⟩,
  ⟨787382880909070739406668311515536234931644678253025001, 3, 0, 0, 3, 0, 0⟩,
  ⟨1938808307862646531180416978644092534415005053597259153, 3, 0, 1, 2, 0, 0⟩,
  ⟨1410307194981869722443077663295475743921377378525878678, 3, 0, 2, 1, 0, 0⟩,
  ⟨194589603372272266756407889338441206194267003181644526, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(723934927367256560650571645278814480345437395208091/138859302016429514840638496913868800000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(723934927367256560650571645278814480345437395208091/138859302016429514840638496913868800000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1CapFlat.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1CapFlat.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper1CapFlatLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper1HeadZeroLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-423086167986637211308247225244094462619/2672893893857100776000000000000000000000)], [(88324099790017101331352071059967637/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(17750450005981967/3180280000000000)], [(-3214751650358371288308056710407908089150691/191019562086800180429019625500000000000000)], [(3089014552323841708582475383692007825965551/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-572684643121184768113360504327645192099309/191019562086800180429019625500000000000000)], [(104204275423512313887356824997694645533603/12583413652467961885761667829812500000000)], [(-118273125/20353792)]], [[(108293424099618781603825118132872771/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-18660350710606719795020025811118252864161583494139/3031862489441692463769399495936000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 103083324641017543768159582861824000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨3947103499923007195873678306051659348528046132277941, 0, 3, 0, 3, 0, 0⟩,
  ⟨8587438260184828985629751711751223974370775340739133, 0, 3, 1, 2, 0, 0⟩,
  ⟨5542528045382131491777617557001464136349223047261918, 0, 3, 2, 1, 0, 0⟩,
  ⟨634451924160628473030680877578020597381493838800726, 0, 3, 3, 0, 0, 0⟩,
  ⟨13096386722639163814036393384623198647938278314112031, 1, 2, 0, 3, 0, 0⟩,
  ⟨28846417441070046649379509413731046078361878429606583, 1, 2, 1, 2, 0, 0⟩,
  ⟨18892173186433059972728758270851816863323775691039898, 1, 2, 2, 1, 0, 0⟩,
  ⟨2325907935357829247469762389368359037900175575545346, 1, 2, 3, 0, 0, 0⟩,
  ⟨14441008927662232267053465917925684874051316317401119, 2, 1, 0, 3, 0, 0⟩,
  ⟨32172460870693353468439038981774642203215587905980087, 2, 1, 1, 2, 0, 0⟩,
  ⟨21364199558617258521692098230606504192156502120230042, 2, 1, 2, 1, 0, 0⟩,
  ⟨2803502633176485227447355283177962812367230531651074, 2, 1, 3, 0, 0, 0⟩,
  ⟨5293660870791290126251139402135440336161591573376693, 3, 0, 0, 3, 0, 0⟩,
  ⟨11919287187343779236770446968138704383786007130541629, 3, 0, 1, 2, 0, 0⟩,
  ⟨8020359915101973472822123205100035749743471789881054, 3, 0, 2, 1, 0, 0⟩,
  ⟨1113981787824498930368662334168919133369056232716118, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(18660350710606719795020025811118252864161583494139/3031862489441692463769399495936000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(18660350710606719795020025811118252864161583494139/3031862489441692463769399495936000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadZero.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadZero.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper1HeadZeroLeaf000


namespace OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper1HeadCapBoundaryLeaf000
open Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def nPolynomial : RationalPolynomial3 := [[[(-406861570049411371362314349088955740819/2672893893857100776000000000000000000000)], [(83398225653477946888564101069792693/213831511508568062080000000000000000)], [(-366381908187431597724833614112097/1368521673654835597312000000000000)]], [[(36460099355572492531999421490692967/6682234734642751940000000000000000)], [(-5830920832885289147953519563056796636689/362465962214042088100606500000000000000)], [(2951253188005627461078870205013762779503199/201334618439487390172186685277000000000000)], [(-39424375/10176896)]], [[(-1308110412227842033545330302362422113311/362465962214042088100606500000000000000)], [(115132739137055113882426638417569026341397/12583413652467961885761667829812500000000)], [(-118273125/20353792)]], [[(49974573088905019894931819367127229/316535994377047602997513875000000000)]]]
def nReduced : RationalPolynomial3 := nPolynomial.add [[[(-17475824668740466905778603516542285872942153513083/3031862489441692463769399495936000000000000000000000)]]]
def nBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def nScale : ℚ := 103083324641017543768159582861824000000000000000000000
def nCertificate : TensorBernstein3 := [
  ⟨2912065381696464497424649793957617159348708341542837, 0, 3, 0, 3, 0, 0⟩,
  ⟨6974884089281225627281649518683248662072749787004221, 0, 3, 1, 2, 0, 0⟩,
  ⟨4924738107281618233644335518011948135529074664906206, 0, 3, 2, 1, 0, 0⟩,
  ⟨594178038737175874796472519562437719680033219444822, 0, 3, 3, 0, 0, 0⟩,
  ⟨9583460745116377874623733480589353636606094229517087, 1, 2, 0, 3, 0, 0⟩,
  ⟨23121544446422349198745833373481450511257668468675511, 1, 2, 1, 2, 0, 0⟩,
  ⟨16463627703722038012342039300280900412819233109068186, 1, 2, 2, 1, 0, 0⟩,
  ⟨2109309469771718798304059555013193143167658869909762, 1, 2, 3, 0, 0, 0⟩,
  ⟨10478118585161557463473160512327911245681947688974111, 2, 1, 0, 3, 0, 0⟩,
  ⟨25446200340919592962186607641067201593217277529092023, 2, 1, 1, 2, 0, 0⟩,
  ⟨18258582527522596075565948129045498987968969365219738, 2, 1, 2, 1, 0, 0⟩,
  ⟨2461255789354908483993331116726624589808639525101826, 2, 1, 3, 0, 0, 0⟩,
  ⟨3807616249991280566244511489230277010168054363190197, 3, 0, 0, 3, 0, 0⟩,
  ⟨9302219068527378830633727776871306469262836533991741, 3, 0, 1, 2, 0, 0⟩,
  ⟨6722372015831085736779548337378853435909288607628766, 3, 0, 2, 1, 0, 0⟩,
  ⟨947017386570002040456178744809971408064506436827222, 3, 0, 3, 0, 0, 0⟩]
noncomputable def n (p z dummy : ℝ) : ℝ := nPolynomial.eval p z dummy

theorem nChecked : nCertificate.scaledBoxCheck nScale nReduced nBox=true := by
  decide +kernel

theorem n_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<n p z dummy := by
  have hx : ∀ i,(nBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [nBox,RatInterval.Contains] using hp
    · simpa [nBox,RatInterval.Contains] using hz
    · simpa [nBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound nChecked ![p, z, dummy] hx
  have he : nReduced.eval p z dummy=n p z dummy-(17475824668740466905778603516542285872942153513083/3031862489441692463769399495936000000000000000000000) := by
    norm_num [nReduced,RationalPolynomial3.eval_add,n,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤nReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(17475824668740466905778603516542285872942153513083/3031862489441692463769399495936000000000000000000000) := by norm_num
  linarith only [hh,hm]

def dPolynomial : RationalPolynomial3 := [[[1]]]
def dReduced : RationalPolynomial3 := dPolynomial.add [[[(-1/2)]]]
def dBox : Fin 3→RatInterval := ![⟨(391/500), (41/50)⟩, ⟨(7/8), (97/100)⟩, ⟨0, 1⟩]
def dScale : ℚ := 2
def dCertificate : TensorBernstein3 := [
  ⟨1, 0, 0, 0, 0, 0, 0⟩]
noncomputable def d (p z dummy : ℝ) : ℝ := dPolynomial.eval p z dummy

theorem dChecked : dCertificate.scaledBoxCheck dScale dReduced dBox=true := by
  decide +kernel

theorem d_pos {p z dummy : ℝ}
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
    (hdummy : dummy∈Icc 0 1)
    : 0<d p z dummy := by
  have hx : ∀ i,(dBox i).Contains (![p, z, dummy] i) := by
    intro i
    fin_cases i
    · simpa [dBox,RatInterval.Contains] using hp
    · simpa [dBox,RatInterval.Contains] using hz
    · simpa [dBox,RatInterval.Contains] using hdummy
  have hh := TensorBernstein3.scaledBoxCheck_sound dChecked ![p, z, dummy] hx
  have he : dReduced.eval p z dummy=d p z dummy-(1/2) := by
    norm_num [dReduced,RationalPolynomial3.eval_add,d,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval] <;> ring
  change 0≤dReduced.eval p z dummy at hh
  rw [he] at hh
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,hm]

theorem numerator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadCapBoundary.numerator p z dummy := by
  exact n_pos hp hz hdummy

theorem denominator_pos {p z dummy : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hdummy : dummy∈Icc (0:ℝ) (1))
    : 0<OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadCapBoundary.denominator p z dummy := by
  exact d_pos hp hz hdummy

end OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper1HeadCapBoundaryLeaf000
