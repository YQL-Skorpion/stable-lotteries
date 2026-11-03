import OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Batch0000
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0001_0004

set_option Elab.async false

namespace OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Batch0001
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cell8_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.flow,1,⟨1813896400928992546218711086905144198992530243584,1814748232718823624338800256002466415815914684416⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-3884064009080571792655708247322797123784,3884064009080571792655708247322797123784⟩,⟨11187784778426530987790460187144908376334395532176,11234434912566945308575070662427151519605621414957⟩,⟨622309916171921547654378426617298741988862872030,633666098636679262824159669290872158633362002622⟩,⟨32421402449755121628022111225030548127119216476160,33028986342012408056773604244648246678911379832832⟩⟩
theorem link8_1_checked : cell8_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert8 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.start)/500000)=true := by decide +kernel
def cell8_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.flow,2,⟨1813896400928992546218711086905144198992530243584,1814748232718823624338800256002466415815914684416⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-3884064009080571792655708247322797123784,3884064009080571792655708247322797123784⟩,⟨11190767756881999361741560714847001027263296322813,11246137591045658294628244783408969656291736753879⟩,⟨901712879013308376852863190065345479118797049766,912805877532059747519323193850223318233610748652⟩,⟨46977873593995033670236574375882647992976531259392,47578768208370988544609262071700492886095519809536⟩⟩
theorem link8_2_checked : cell8_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert8 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.start)/500000)=true := by decide +kernel
def cell9_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.cell.flow,1,⟨1813045810765180100903929805821178304633241600000,1813897245185457255399676908098910697709226688512⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-4381228006594062427980443459557708562052,4381228006594062427980443459557708562052⟩,⟨11191175490126983228725827871781995072284851474606,11237860652823966025318236997731528070626387075933⟩,⟨623019617336279229496673760064109126615765542637,634384032174039747677663529424740871673349890081⟩,⟨32443155904167435940078550756025114900578412003328,33050902064612265516157348898154400551752007942144⟩⟩
theorem link9_1_checked : cell9_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert9 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.start)/500000)=true := by decide +kernel
def cell9_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.cell.flow,2,⟨1813045810765180100903929805821178304633241600000,1813897245185457255399676908098910697709226688512⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-4381228006594062427980443459557708562052,4381228006594062427980443459557708562052⟩,⟨11195638570149600727573232984365933442025742443828,11251052567082869103328027549467530297106305368240⟩,⟨903105582709740401829908727358375231609320711058,914210577219819785965195084827473679793387202699⟩,⟨47028367795408687263344684549469127378732333400064,47629641087826632943387701432201552683347608600576⟩⟩
theorem link9_2_checked : cell9_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert9 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.start)/500000)=true := by decide +kernel
def cell10_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.flow,1,⟨1812272605662891285794290235525238322852565876736,1813046516295482807976748798085442431739949481984⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-4833362563703428514815987134346970023268,4833362563703428514815987134346970023268⟩,⟨11196521235549289718695393420593334237503042096145,11239008695551333962911402661181964096013349286007⟩,⟨624212089599006270865071960793931428484828038509,634552747909343968740590642724148950138668762719⟩,⟨32491390155224620147027183434343919499936243122176,33044187003084851636717842823227827591911969914880⟩⟩
theorem link10_1_checked : cell10_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert10 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.start)/500000)=true := by decide +kernel
def cell10_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.flow,2,⟨1812272605662891285794290235525238322852565876736,1813046516295482807976748798085442431739949481984⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-4833362563703428514815987134346970023268,4833362563703428514815987134346970023268⟩,⟨11202801468925881701697030185826368420305051746708,11253233037553397040092141436624236087432952530119⟩,⟨904939123155468385510165832282043406913341985961,915047363299358027047729338330676434631847561130⟩,⟨47103750710202316046922023710573688195693892599808,47650878115030086246067992450860347395175205568512⟩⟩
theorem link10_2_checked : cell10_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert10 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.start)/500000)=true := by decide +kernel
def cell11_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.cell.flow,1,⟨1811499728561314118855750547155156563347365691392,1812273311229598458933115526757957283438909194240⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-5285497120812794601651530809136231484483,5285497120812794601651530809136231484483⟩,⟨11199604522937119272021363802559062829493231120260,11242121025087940883646472725295584528837467297415⟩,⟨624859387295721027646252534834008620344372549772,635206869635928310394144155189175002308210512789⟩,⟨32511212092271015537515357157252830004831718473728,33064143627371888613137203891026536289824768262144⟩⟩
theorem link11_1_checked : cell11_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert11 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.start)/500000)=true := by decide +kernel
def cell11_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.cell.flow,2,⟨1811499728561314118855750547155156563347365691392,1812273311229598458933115526757957283438909194240⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-5285497120812794601651530809136231484483,5285497120812794601651530809136231484483⟩,⟨11207247104669059150742531054917939103689251725775,11257715336116070159504519329791596666097766724653⟩,⟨906209507893492825727735862975238148580100645656,916327703933108510834373783629106581347092814109⟩,⟨47149759935573944879013602620178032657111577526272,47697201758662660202985255023575595868960025739264⟩⟩
theorem link11_2_checked : cell11_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert11 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.start)/500000)=true := by decide +kernel
def cell12_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.flow,1,⟨1810804185152922496476692602766538795525676728320,1811500308316747718758150776744441062036783235072⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-5692555389628922359447932167311606533213,5692555389628922359447932167311606533213⟩,⟨11204648517464747866894673603008651103972666668236,11242951295515050102238734255210585918242168566013⟩,⟨625990319175341714808166375109053601390286248714,635310714417247457599355714839346054387133038842⟩,⟨32557548319817698371581801009564246997798284689408,33055443767014669012626043818905518199063674093568⟩⟩
theorem link12_1_checked : cell12_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert12 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.start)/500000)=true := by decide +kernel
def cell12_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.flow,2,⟨1810804185152922496476692602766538795525676728320,1811500308316747718758150776744441062036783235072⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-5692555389628922359447932167311606533213,5692555389628922359447932167311606533213⟩,⟨11213989057995493506411472495728704258933288852943,11259455630384401298800029408979893957437325219509⟩,⟨907921643982788806706160263179013007232653969870,917038484627183097633512010630282016015013655813⟩,⟨47220703785875273692552821355321377595240162000896,47713839438079746030149348577892549833916072067072⟩⟩
theorem link12_2_checked : cell12_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert12 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.start)/500000)=true := by decide +kernel
def cell13_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.cell.flow,1,⟨1810108907101709586283729085797669002525018161152,1810804764932508734147851274789834489613787332608⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-6099613658445050117244333525486981581943,6099613658445050117244333525486981581943⟩,⟨11207424297304562470448061720025022649893059093645,11245750667883673367422285079854360864211908837603⟩,⟨626574646306992604131738276028514318847691569664,635900584063194069696273811663384851109679154681⟩,⟨32575426323109892225814961690765835603640380817408,33073431309742048559213321872944391872140791513088⟩⟩
theorem link13_1_checked : cell13_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert13 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.start)/500000)=true := by decide +kernel
def cell13_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.cell.flow,2,⟨1810108907101709586283729085797669002525018161152,1810804764932508734147851274789834489613787332608⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-6099613658445050117244333525486981581943,6099613658445050117244333525486981581943⟩,⟨11218004684930282007265149800387456479925810685177,11263501075466008278110476222395363218114023896427⟩,⟨909068543761728317552483713370092422292900204464,918193479524102274496051480611194906045817164058⟩,⟨47262199693857078845528637678042309261016659132416,47755591123072509474549368611606743688387514859520⟩⟩
theorem link13_2_checked : cell13_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert13 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.start)/500000)=true := by decide +kernel
def cell14_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.flow,1,⟨1809333894913503096072143756559657437532541419520,1810109618508212635850210861725139027181101383680⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-6553536314546568096514155604914272343409,6553536314546568096514155604914272343409⟩,⟨11208157134013831071600205388998551386479464105316,11250923987312943690012874167002079708932426261579⟩,⟨626658454868467851488374194731375515903855272765,637063142639455805258229784229496189738441115731⟩,⟨32565834035114869692060513923989007096572966600704,33121176892956767594164139329140244817447191838720⟩⟩
theorem link14_1_checked : cell14_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert14 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.start)/500000)=true := by decide +kernel
def cell14_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.flow,2,⟨1809333894913503096072143756559657437532541419520,1810109618508212635850210861725139027181101383680⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-6553536314546568096514155604914272343409,6553536314546568096514155604914272343409⟩,⟨11219644430162159607244993902231673325543831802686,11270412225591890758369688536266540328042363268517⟩,⟨909759627218029381786366760100291302401109322805,919943399455526628453635786368272581341291411431⟩,⟨47277877671707927151341302102938515537222134923264,47828237558291758920821904147780747071871013355520⟩⟩
theorem link14_2_checked : cell14_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert14 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.start)/500000)=true := by decide +kernel
def cell15_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.cell.flow,1,⟨1808559212057447197706378307092817614460413804544,1809334606358459910154860354513558101613065797632⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-7007458970648086075783977684341563104875,7007458970648086075783977684341563104875⟩,⟨11211249409899299450961938340502968017325264138283,11254045666361262051663177694599897681997629598373⟩,⟨627311110134114253640997285779152758809941048840,637722704261695364040414331222334427595769032837⟩,⟨32585792795721789434070908274594867401821209493504,33141272190019150353345083736070531818183953743872⟩⟩
theorem link15_1_checked : cell15_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert15 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.start)/500000)=true := by decide +kernel
def cell15_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.cell.flow,2,⟨1808559212057447197706378307092817614460413804544,1809334606358459910154860354513558101613065797632⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-7007458970648086075783977684341563104875,7007458970648086075783977684341563104875⟩,⟨11224133395754989099022242089376851311754304297608,11274938396913212803370293125615543977653749793784⟩,⟨911041101513379870906647421556872451212069293872,921234971906126569776264484123420332971255177538⟩,⟨47324201460374067077489553171944971614510439727104,47874880350308243923359389389281105082869912436736⟩⟩
theorem link15_2_checked : cell15_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0001.cert15 ((ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.start)/500000)=true := by decide +kernel
def cells : List Transport.ReferencePositionCell := [cell8_1,cell8_2,cell9_1,cell9_2,cell10_1,cell10_2,cell11_1,cell11_2,cell12_1,cell12_2,cell13_1,cell13_2,cell14_1,cell14_2,cell15_1,cell15_2]
theorem checked : cells.all (fun c => c.check scale 1)=true := by decide +kernel
theorem weight8_member : ReferenceWeightData.CoarseLowerShape.Batch0001.cert8∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound8_1_checked : cell8_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound8_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell8_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight8_member hc link8_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound8_1_checked
theorem bound8_2_checked : cell8_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound8_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell8_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight8_member hc link8_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound8_2_checked
theorem weight9_member : ReferenceWeightData.CoarseLowerShape.Batch0001.cert9∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound9_1_checked : cell9_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound9_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell9_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight9_member hc link9_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound9_1_checked
theorem bound9_2_checked : cell9_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound9_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell9_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight9_member hc link9_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound9_2_checked
theorem weight10_member : ReferenceWeightData.CoarseLowerShape.Batch0001.cert10∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound10_1_checked : cell10_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound10_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell10_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight10_member hc link10_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound10_1_checked
theorem bound10_2_checked : cell10_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound10_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell10_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight10_member hc link10_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound10_2_checked
theorem weight11_member : ReferenceWeightData.CoarseLowerShape.Batch0001.cert11∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound11_1_checked : cell11_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound11_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell11_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight11_member hc link11_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound11_1_checked
theorem bound11_2_checked : cell11_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound11_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell11_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight11_member hc link11_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound11_2_checked
theorem weight12_member : ReferenceWeightData.CoarseLowerShape.Batch0001.cert12∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound12_1_checked : cell12_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound12_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell12_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight12_member hc link12_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound12_1_checked
theorem bound12_2_checked : cell12_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound12_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell12_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight12_member hc link12_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound12_2_checked
theorem weight13_member : ReferenceWeightData.CoarseLowerShape.Batch0001.cert13∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound13_1_checked : cell13_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound13_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell13_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight13_member hc link13_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound13_1_checked
theorem bound13_2_checked : cell13_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound13_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell13_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight13_member hc link13_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound13_2_checked
theorem weight14_member : ReferenceWeightData.CoarseLowerShape.Batch0001.cert14∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound14_1_checked : cell14_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound14_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell14_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight14_member hc link14_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound14_1_checked
theorem bound14_2_checked : cell14_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound14_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell14_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight14_member hc link14_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound14_2_checked
theorem weight15_member : ReferenceWeightData.CoarseLowerShape.Batch0001.cert15∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound15_1_checked : cell15_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound15_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell15_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight15_member hc link15_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound15_1_checked
theorem bound15_2_checked : cell15_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound15_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell15_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight15_member hc link15_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound15_2_checked
theorem actual_bounds : ∀ w∈ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,∀ z∈Set.Ioc (w.cell.flow.segment.left.z:ℝ) w.cell.flow.segment.right.z,
    |force 1 z|≤100 ∧ |force 2 z|≤100 := by
  intro w hw
  simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>⟨actual_bound8_1 hz,actual_bound8_2 hz⟩
  · exact fun z hz=>⟨actual_bound9_1 hz,actual_bound9_2 hz⟩
  · exact fun z hz=>⟨actual_bound10_1 hz,actual_bound10_2 hz⟩
  · exact fun z hz=>⟨actual_bound11_1 hz,actual_bound11_2 hz⟩
  · exact fun z hz=>⟨actual_bound12_1 hz,actual_bound12_2 hz⟩
  · exact fun z hz=>⟨actual_bound13_1 hz,actual_bound13_2 hz⟩
  · exact fun z hz=>⟨actual_bound14_1 hz,actual_bound14_2 hz⟩
  · exact fun z hz=>⟨actual_bound15_1 hz,actual_bound15_2 hz⟩
end OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Batch0001

namespace OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Batch0002
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cell16_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.flow,1,⟨1807712429099375904900759333780160274759562559488,1808560055352292289317624374283591767417650413568⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-7503849232174856413566785931885022823515,7503849232174856413566785931885022823515⟩,⟨11212487785066392409848274604949283730697909666030,11259321725068684510603821801036067041331737980823⟩,⟨627510259462514943002356367962770205097557512935,638902038247761936580601900169101581034426181592⟩,⟨32580875654171834301239262894832285575467522588672,33188346641281056503474456680057774632159485624320⟩⟩
theorem link16_1_checked : cell16_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert16 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.start)/500000)=true := by decide +kernel
def cell16_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.flow,2,⟨1807712429099375904900759333780160274759562559488,1808560055352292289317624374283591767417650413568⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-7503849232174856413566785931885022823515,7503849232174856413566785931885022823515⟩,⟨11226469293543739195912189207763271381899856142233,11282067879666757146797224059659000758671135915857⟩,⟨911909567190813562190022326699754688286737661437,923067170057762881702917190446508846382207167667⟩,⟨47347135155627087966481412660671302755026900877312,47949561168444909735486800781931915871155996590080⟩⟩
theorem link16_2_checked : cell16_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert16 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.start)/500000)=true := by decide +kernel
def cell17_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.cell.flow,1,⟨1806866039136499392453925165957856570451202932736,1807713272449268354398450021435812090101809283072⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-8000239493701626751349594179428482542156,8000239493701626751349594179428482542156⟩,⟨11215865987336259863009286129781174724403190458530,11262735176207211413213437866233437555394031130275⟩,⟨628225328330681387953543811329625968080064174031,639625384959188257408489394290651637952348376138⟩,⟨32602730360805624966742925590846095333710035419136,33210365085691207107069006410461206284779399413760⟩⟩
theorem link17_1_checked : cell17_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert17 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.start)/500000)=true := by decide +kernel
def cell17_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.cell.flow,2,⟨1806866039136499392453925165957856570451202932736,1807713272449268354398450021435812090101809283072⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-8000239493701626751349594179428482542156,8000239493701626751349594179428482542156⟩,⟨11231391950331958445630187524292579545081054441576,11287035196876192266213157547445958698244255487315⟩,⟨913314108872357988726159799996989226140374391380,924483829853917540054406680469864116311468953182⟩,⟨47397857410843840338557135653752904777047096688640,48000666202125088570830595890403771545655739154432⟩⟩
theorem link17_2_checked : cell17_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert17 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.start)/500000)=true := by decide +kernel
def cell18_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.flow,1,⟨1806325848610154506551681696417184936790406987776,1806866406727663125803580147076235190930526699520⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-8317170592413109367255677702832014541339,8317170592413109367255677702832014541339⟩,⟨11227089427841849613234077366636128731298550853627,11257032511108244871380428506166397623906985853006⟩,⟨630868308724341558929368749625639409635138774156,638150246859131836350247792998817000130445443731⟩,⟨32730103730167006209347256849973275496776302854144,33118251412806034407628986873676226429090235678720⟩⟩
theorem link18_1_checked : cell18_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert18 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.start)/500000)=true := by decide +kernel
def cell18_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.flow,2,⟨1806325848610154506551681696417184936790406987776,1806866406727663125803580147076235190930526699520⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-8317170592413109367255677702832014541339,8317170592413109367255677702832014541339⟩,⟨11245471338652647560545206520728639643249210521036,11281020055903863519917917876688353113187729165197⟩,⟨916480654266276508844690427188222192700422302169,923617680023934873793304162811349908170823498425⟩,⟨47547970647432210038951777193031166262757686247424,47933228487087077239380361221793123119503014625280⟩⟩
theorem link18_2_checked : cell18_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert18 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.start)/500000)=true := by decide +kernel
def cell19_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.cell.flow,1,⟨1805785818016847732770233192672261418386892783616,1806326216208781708359227099406641891681373257728⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-8634101691124591983161761226235546540521,8634101691124591983161761226235546540521⟩,⟨11229249356151351997704368588235259010464857592182,11259206838684099311867877968658928674792397303068⟩,⟨631326746311827688030286148226023139440509490159,638612065429556620954009767040223286781797535729⟩,⟨32744095514577004870187433089137837321366630563840,33132310281413038768019243141143851400269848903680⟩⟩
theorem link19_1_checked : cell19_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert19 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.start)/500000)=true := by decide +kernel
def cell19_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.cell.flow,2,⟨1805785818016847732770233192672261418386892783616,1806326216208781708359227099406641891681373257728⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-8634101691124591983161761226235546540521,8634101691124591983161761226235546540521⟩,⟨11248628003495357003079652017161945248475125311569,11284194984849218007737349945152652214430903217981⟩,⟨917380833661641482137272442498461405211404234914,924522814025423592840416317899677086330474522479⟩,⟨47580443562962657067074023877177646354371406987264,47965858167986972741890569688632865806753896333312⟩⟩
theorem link19_2_checked : cell19_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert19 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.start)/500000)=true := by decide +kernel
def cell20_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.flow,1,⟨1805014384405151164697019221102409752646879543296,1805786527270610720032600944295902210583359913984⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-9087000575928846439843488129001564163490,9087000575928846439843488129001564163490⟩,⟨11225457243868988674582641416565251632213505526064,11268291906216871055661412874189940364741478048054⟩,⟨630325328377299508427130653523169002698767203478,640740670626570868799608705209753260391875925191⟩,⟨32678190130798430230083138657888669866504950382592,33232814040538369258383963337396227467501446889472⟩⟩
theorem link20_1_checked : cell20_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert20 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.start)/500000)=true := by decide +kernel
def cell20_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.flow,2,⟨1805014384405151164697019221102409752646879543296,1805786527270610720032600944295902210583359913984⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-9087000575928846439843488129001564163490,9087000575928846439843488129001564163490⟩,⟨11244851061338617941806447245185959552078005736919,11295706757587320130025934111706619658839551262309⟩,⟨916947387000693759617033773715086960253033045820,927160821757394953837847636390325508963856637954⟩,⟨47537645623399318421910949435035166176584186986496,48088350798567519217736864028292054434690797404160⟩⟩
theorem link20_2_checked : cell20_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert20 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.start)/500000)=true := by decide +kernel
def cell21_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.cell.flow,1,⟨1804243276805318490066873437057998098251617665024,1805015093699192155053271322134043841265848549376⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-9539899460733100896525215031767581786459,9539899460733100896525215031767581786459⟩,⟨11228538048695315229900920477407836400724448538418,11271402174037257380657689391332811777340005339848⟩,⟨630980677211475474173390945189696544361212654703,641402936439458682660794871133429962351344633055⟩,⟨32698190709592356425286775264317503126360272404480,33252951700239216447433587497964902439622390317056⟩⟩
theorem link21_1_checked : cell21_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert21 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.start)/500000)=true := by decide +kernel
def cell21_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.cell.flow,2,⟨1804243276805318490066873437057998098251617665024,1805015093699192155053271322134043841265848549376⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-9539899460733100896525215031767581786459,9539899460733100896525215031767581786459⟩,⟨11249367962577113511009504115416772249729412451645,11300261068949011646229543933851270031393657115356⟩,⟨918234987081672125611187406856333224349358904055,928458568091028422195278546484910860977409693576⟩,⟨47584062233973031086896265896282772680899892871168,48135088066671171810504558581133539022302355652608⟩⟩
theorem link21_2_checked : cell21_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert21 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.start)/500000)=true := by decide +kernel
def cell22_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.flow,1,⟨1803549317280376014268656595796332705965750091776,1804243859454564174929053685209793910651133886464⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-9947650267413220955022171674838615286754,9947650267413220955022171674838615286754⟩,⟨11233596909921126932352392843176730346888059298764,11272213190464997907345514885127016614436036379755⟩,⟨632122964674000118396304356276096317353333255717,641510799570389961671653078085657300880960767587⟩,⟨32744785933285068953323763414777527071390461591552,33244333450404606549257200131794591295878446710784⟩⟩
theorem link22_1_checked : cell22_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert22 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.start)/500000)=true := by decide +kernel
def cell22_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.flow,2,⟨1803549317280376014268656595796332705965750091776,1804243859454564174929053685209793910651133886464⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-9947650267413220955022171674838615286754,9947650267413220955022171674838615286754⟩,⟨11256198714194380015071280981469285407509766740496,11302048641415566307402953741153780411564398777448⟩,⟨919968730126972501061577184370248209154892920921,929180649867134129316311525951604204138030508624⟩,⟨47655570125066904007474828181577314640075369218048,48151941079581502202836541998824555418324362592256⟩⟩
theorem link22_2_checked : cell22_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert22 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.start)/500000)=true := by decide +kernel
def cell23_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.cell.flow,1,⟨1802855621515573351237800839138512382801588781056,1803549899956648462094258975170708425164403507200⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-10355401074093341013519128317909648787049,10355401074093341013519128317909648787049⟩,⟨11236370557642006407397540268770170146718248308449,11275010772882727117940480339688482812856240426538⟩,⟨632714571590616089918684215932241462332080506927,642108024702454495041421260053260590169012316631⟩,⟨32762825423016696484011480227846111515886265303040,33262484428647250035804605264657190274648848203776⟩⟩
theorem link23_1_checked : cell23_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert23 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.start)/500000)=true := by decide +kernel
def cell23_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.cell.flow,2,⟨1802855621515573351237800839138512382801588781056,1803549899956648462094258975170708425164403507200⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-10355401074093341013519128317909648787049,10355401074093341013519128317909648787049⟩,⟨11260278665383833714551793839766289548530098609845,11306159018792742960652898996192768467613530822996⟩,⟨921131197701305841076444289278114061112662668267,930351367551656922903725729692694773705041955266⟩,⟨47697434456088946560544496625651723903457166360576,48194066263501467693562451361749369732582298615808⟩⟩
theorem link23_2_checked : cell23_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0002.cert23 ((ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.start)/500000)=true := by decide +kernel
def cells : List Transport.ReferencePositionCell := [cell16_1,cell16_2,cell17_1,cell17_2,cell18_1,cell18_2,cell19_1,cell19_2,cell20_1,cell20_2,cell21_1,cell21_2,cell22_1,cell22_2,cell23_1,cell23_2]
theorem checked : cells.all (fun c => c.check scale 1)=true := by decide +kernel
theorem weight16_member : ReferenceWeightData.CoarseLowerShape.Batch0002.cert16∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound16_1_checked : cell16_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound16_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell16_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight16_member hc link16_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound16_1_checked
theorem bound16_2_checked : cell16_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound16_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell16_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight16_member hc link16_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound16_2_checked
theorem weight17_member : ReferenceWeightData.CoarseLowerShape.Batch0002.cert17∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound17_1_checked : cell17_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound17_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell17_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight17_member hc link17_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound17_1_checked
theorem bound17_2_checked : cell17_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound17_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell17_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight17_member hc link17_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound17_2_checked
theorem weight18_member : ReferenceWeightData.CoarseLowerShape.Batch0002.cert18∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound18_1_checked : cell18_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound18_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell18_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight18_member hc link18_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound18_1_checked
theorem bound18_2_checked : cell18_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound18_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell18_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight18_member hc link18_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound18_2_checked
theorem weight19_member : ReferenceWeightData.CoarseLowerShape.Batch0002.cert19∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound19_1_checked : cell19_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound19_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell19_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight19_member hc link19_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound19_1_checked
theorem bound19_2_checked : cell19_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound19_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell19_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight19_member hc link19_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound19_2_checked
theorem weight20_member : ReferenceWeightData.CoarseLowerShape.Batch0002.cert20∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound20_1_checked : cell20_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound20_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell20_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight20_member hc link20_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound20_1_checked
theorem bound20_2_checked : cell20_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound20_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell20_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight20_member hc link20_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound20_2_checked
theorem weight21_member : ReferenceWeightData.CoarseLowerShape.Batch0002.cert21∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound21_1_checked : cell21_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound21_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell21_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight21_member hc link21_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound21_1_checked
theorem bound21_2_checked : cell21_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound21_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell21_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight21_member hc link21_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound21_2_checked
theorem weight22_member : ReferenceWeightData.CoarseLowerShape.Batch0002.cert22∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound22_1_checked : cell22_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound22_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell22_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight22_member hc link22_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound22_1_checked
theorem bound22_2_checked : cell22_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound22_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell22_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight22_member hc link22_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound22_2_checked
theorem weight23_member : ReferenceWeightData.CoarseLowerShape.Batch0002.cert23∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound23_1_checked : cell23_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound23_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell23_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight23_member hc link23_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound23_1_checked
theorem bound23_2_checked : cell23_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound23_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell23_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight23_member hc link23_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound23_2_checked
theorem actual_bounds : ∀ w∈ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,∀ z∈Set.Ioc (w.cell.flow.segment.left.z:ℝ) w.cell.flow.segment.right.z,
    |force 1 z|≤100 ∧ |force 2 z|≤100 := by
  intro w hw
  simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>⟨actual_bound16_1 hz,actual_bound16_2 hz⟩
  · exact fun z hz=>⟨actual_bound17_1 hz,actual_bound17_2 hz⟩
  · exact fun z hz=>⟨actual_bound18_1 hz,actual_bound18_2 hz⟩
  · exact fun z hz=>⟨actual_bound19_1 hz,actual_bound19_2 hz⟩
  · exact fun z hz=>⟨actual_bound20_1 hz,actual_bound20_2 hz⟩
  · exact fun z hz=>⟨actual_bound21_1 hz,actual_bound21_2 hz⟩
  · exact fun z hz=>⟨actual_bound22_1 hz,actual_bound22_2 hz⟩
  · exact fun z hz=>⟨actual_bound23_1 hz,actual_bound23_2 hz⟩
end OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Batch0002

namespace OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Batch0003
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cell24_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.flow,1,⟨1802161959434646294256603791029575371958469525504,1802856204743152739419155904644012872179396902912⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-10763287137703869343868756206330087557419,10763287137703869343868756206330087557419⟩,⟨11239137690353838725169711698510490148887138843241,11277814570779814123107091892930133476187426735976⟩,⟨633305989656041161650124852093826825011081182011,642706863748548843213665722149150079657947526288⟩,⟨32780832175595615635528235796446662476913201643520,33280700049523318977827933901821065390190527250432⟩⟩
theorem link24_1_checked : cell24_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert24 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.start)/500000)=true := by decide +kernel
def cell24_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.flow,2,⟨1802161959434646294256603791029575371958469525504,1802856204743152739419155904644012872179396902912⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-10763287137703869343868756206330087557419,10763287137703869343868756206330087557419⟩,⟨11264358129687685612777543219115212619731317204832,11310282377377531511607977726069295710710375279191⟩,⟨922294218993791249133830075662518700140658045348,931524570452453889621700167856910143815377417192⟩,⟨47739282018045266993035027354375348581461303230464,48236280538504678284017439224135682521544160968704⟩⟩
theorem link24_2_checked : cell24_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert24 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.start)/500000)=true := by decide +kernel
def cell25_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.cell.flow,1,⟨1801468560815969061783018102605593072159126716416,1802162542689799205043742657117323016988243525632⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-11171173201314397674218384094750526327788,11171173201314397674218384094750526327788⟩,⟨11241910976140197381651417250204498849171806457384,11280611857513671055335970565646211049100884679242⟩,⟨633899007430207451981194610353487497377910721752,643305514468900395493578422326505944215916902610⟩,⟨32798902930427908631997151742512356531234056175616,33298882671794724755846045103369096530663057653760⟩⟩
theorem link25_1_checked : cell25_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert25 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.start)/500000)=true := by decide +kernel
def cell25_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.cell.flow,2,⟨1801468560815969061783018102605593072159126716416,1802162542689799205043742657117323016988243525632⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-11171173201314397674218384094750526327788,11171173201314397674218384094750526327788⟩,⟨11268450484630315206323138897949057041726960287044,11314405276492674868897667238730413161571645104702⟩,⟨923459704920553438063701373927334638986916970083,932698336626858302563679714500730731523861515379⟩,⟨47781217749517342629980388029287975900277402238976,48278478107163963298067754008427044860449907539968⟩⟩
theorem link25_2_checked : cell25_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert25 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.start)/500000)=true := by decide +kernel
def cell26_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.flow,1,⟨1800698155544599464251894156444777596391383891968,1801469272357275740381892942494271775534093434880⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-11624539598215787880054822806158504563983,11624539598215787880054822806158504563983⟩,⟨11242684892417827458965849918085661548260104863304,11285729033616911905733119966334346444696688074031⟩,⟨634003378738222377166076139566317434208341842368,644463792505810927995530852149395930480203320275⟩,⟨32790274186826823503918958408881253487663936176128,33346005074406689782065042830256670181491354894336⟩⟩
theorem link26_1_checked : cell26_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert26 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.start)/500000)=true := by decide +kernel
def cell26_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.flow,2,⟨1800698155544599464251894156444777596391383891968,1801469272357275740381892942494271775534093434880⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-11624539598215787880054822806158504563983,11624539598215787880054822806158504563983⟩,⟨11270221039807404894340828782246209189405086843314,11321333635511333493758774526652951703381589361979⟩,⟨924178577592438680439615354963405580690237315730,934455722217746942268689982204504615676414081029⟩,⟨47797963403656201025832046795869157989715938377728,48350837207255482275359697263126137978815650988032⟩⟩
theorem link26_2_checked : cell26_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert26 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.start)/500000)=true := by decide +kernel
def cell27_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.cell.flow,1,⟨1799928075140968055109614010870735393473429504000,1800698867128495143540830024955919623453365239808⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-12077905995117178085891261517566482800179,12077905995117178085891261517566482800179⟩,⟨11245764436225636106773988326421051922357946481894,11288838294914952864043188478737623845382025064122⟩,⟨634663601919381088286011109452870214571540237131,645130989249084338346264065542021444415858798393⟩,⟨32810382776751495223271859736054834265520301146112,33366252200770436278877170330942739351062989242368⟩⟩
theorem link27_1_checked : cell27_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert27 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.start)/500000)=true := by decide +kernel
def cell27_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.cell.flow,2,⟨1799928075140968055109614010870735393473429504000,1800698867128495143540830024955919623453365239808⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-12077905995117178085891261517566482800179,12077905995117178085891261517566482800179⟩,⟨11274780799278300399457899290563780450452654294529,11325931258315268989380099097500844417153620406919⟩,⟨925476605993564978123594063415162263638449239788,935764012632489080234458021211583343735438006676⟩,⟨47844626656158632852157220244099038432537471877120,48397824897785275157878902551910993641167552249856⟩⟩
theorem link27_2_checked : cell27_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert27 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.start)/500000)=true := by decide +kernel
def cell28_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.flow,1,⟨1799235034928650943580185561941477294733975879680,1799928659575673479528342704401871268781720862720⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-12486080364703237945330967706586345668829,12486080364703237945330967706586345668829⟩,⟨11250832490575759345815683480609022664444021633471,11289637920124865122883138233582199161347486425189⟩,⟨635812757121513705622895808319821892206879410493,645241292764637349628273074196706611665462621288⟩,⟨32857134712414218559154218910527198922443830853632,33357683186729144230753065113939444092265264316416⟩⟩
theorem link28_1_checked : cell28_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert28 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.start)/500000)=true := by decide +kernel
def cell28_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.flow,2,⟨1799235034928650943580185561941477294733975879680,1799928659575673479528342704401871268781720862720⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-12486080364703237945330967706586345668829,12486080364703237945330967706586345668829⟩,⟨11281665044525818952740754408685129235612844627806,11327747176966041811893777128033468777271654545246⟩,⟨927223436950594835904786749533581472736721502461,936492941392986661978637087417079375601520399642⟩,⟨47916476158974194569463032981403059148199737425920,48414808157009698770741074671680546892978858229760⟩⟩
theorem link28_2_checked : cell28_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert28 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.start)/500000)=true := by decide +kernel
def cell29_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.cell.flow,1,⟨1798542257557953803139565766030233383485715775488,1799235619392096009505733304177354853397760573440⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-12894254734289297804770673895606208537479,12894254734289297804770673895606208537479⟩,⟨11253605063991740211968198668695485131652734669861,11292434635169949888890634552429171782784367003066⟩,⟨636408771524545826550392162368047832650939621857,645842971467788549563724613232885241219383458392⟩,⟨32875271844183996520946451216886161446140819537920,33375932992223981892521920099829253237654517972992⟩⟩
theorem link29_1_checked : cell29_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert29 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.start)/500000)=true := by decide +kernel
def cell29_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.cell.flow,2,⟨1798542257557953803139565766030233383485715775488,1799235619392096009505733304177354853397760573440⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-12894254734289297804770673895606208537479,12894254734289297804770673895606208537479⟩,⟨11285783682115744414110005201521655787947100058465,11331896609517796643667230200591264369078975374888⟩,⟨928395335137956472373970324066337689873993386441,937673183949690144456028071950993310053880461061⟩,⟨47958563549809004561505433261535391053611135926272,48457159476524434376899501715489755719079374618624⟩⟩
theorem link29_2_checked : cell29_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert29 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.start)/500000)=true := by decide +kernel
def cell30_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.flow,1,⟨1797669070415811890993513619340786749516619448320,1798543164146083280348585129747481455994507100160⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-13408944605442345713640682616651571209098,13408944605442345713640682616651571209098⟩,⟨11251683094370328650700830031695222308227644669940,11300679583521195272636083657349171616429596315141⟩,⟨635856514902882385994231911147984585976755901590,647758783755879777243327963555198273480060331576⟩,⟨32830796445963517354592392112230602704448512851968,33462055520086777157047735925355874751755969363968⟩⟩
theorem link30_1_checked : cell30_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert30 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.start)/500000)=true := by decide +kernel
def cell30_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.flow,2,⟨1797669070415811890993513619340786749516619448320,1798543164146083280348585129747481455994507100160⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-13408944605442345713640682616651571209098,13408944605442345713640682616651571209098⟩,⟨11284443650305167734288758536243265008114142299079,11342631203521179253633758915317698863213030300551⟩,⟨928515467296336660850908288432823224174476649998,940224671904797592408299891957155994214298067451⟩,⟨47941482305088403738890854618502511006319061762048,48570315691663677115779824617160413851782437928960⟩⟩
theorem link30_2_checked : cell30_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert30 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.start)/500000)=true := by decide +kernel
def cell31_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.cell.flow,1,⟨1796796300326311035154977560383404708574194040832,1797669977073972110632858539750650524499865239552⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-13923634476595393622510691337696933880717,13923634476595393622510691337696933880717⟩,⟨11255173447723611777686525340756761078119251891441,11304208413418129709276986271098599211885593623229⟩,⟨636608883413330402776165406890133412942160710300,648520178597182185088683055064141425141315470809⟩,⟨32853684591513977455703217799323522475837978836992,33485123192363281000131704901020943766075933196288⟩⟩
theorem link31_1_checked : cell31_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert31 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.start)/500000)=true := by decide +kernel
def cell31_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.cell.flow,2,⟨1796796300326311035154977560383404708574194040832,1797669977073972110632858539750650524499865239552⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-13923634476595393622510691337696933880717,13923634476595393622510691337696933880717⟩,⟨11289647835748731837427858807302914401479828818138,11347884530763682238763430250141961939905837992477⟩,⟨929995601597224349189787348599639278296870397992,941718118713230671495352711156718418697927485793⟩,⟨47994592251793511913852201020185989791340348571648,48623846476727458782568783026371715575044185784320⟩⟩
theorem link31_2_checked : cell31_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0003.cert31 ((ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.start)/500000)=true := by decide +kernel
def cells : List Transport.ReferencePositionCell := [cell24_1,cell24_2,cell25_1,cell25_2,cell26_1,cell26_2,cell27_1,cell27_2,cell28_1,cell28_2,cell29_1,cell29_2,cell30_1,cell30_2,cell31_1,cell31_2]
theorem checked : cells.all (fun c => c.check scale 1)=true := by decide +kernel
theorem weight24_member : ReferenceWeightData.CoarseLowerShape.Batch0003.cert24∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound24_1_checked : cell24_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound24_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell24_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight24_member hc link24_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound24_1_checked
theorem bound24_2_checked : cell24_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound24_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell24_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight24_member hc link24_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound24_2_checked
theorem weight25_member : ReferenceWeightData.CoarseLowerShape.Batch0003.cert25∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound25_1_checked : cell25_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound25_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell25_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight25_member hc link25_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound25_1_checked
theorem bound25_2_checked : cell25_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound25_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell25_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight25_member hc link25_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound25_2_checked
theorem weight26_member : ReferenceWeightData.CoarseLowerShape.Batch0003.cert26∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound26_1_checked : cell26_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound26_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell26_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight26_member hc link26_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound26_1_checked
theorem bound26_2_checked : cell26_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound26_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell26_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight26_member hc link26_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound26_2_checked
theorem weight27_member : ReferenceWeightData.CoarseLowerShape.Batch0003.cert27∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound27_1_checked : cell27_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound27_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell27_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight27_member hc link27_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound27_1_checked
theorem bound27_2_checked : cell27_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound27_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell27_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight27_member hc link27_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound27_2_checked
theorem weight28_member : ReferenceWeightData.CoarseLowerShape.Batch0003.cert28∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound28_1_checked : cell28_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound28_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell28_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight28_member hc link28_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound28_1_checked
theorem bound28_2_checked : cell28_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound28_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell28_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight28_member hc link28_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound28_2_checked
theorem weight29_member : ReferenceWeightData.CoarseLowerShape.Batch0003.cert29∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound29_1_checked : cell29_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound29_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell29_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight29_member hc link29_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound29_1_checked
theorem bound29_2_checked : cell29_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound29_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell29_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight29_member hc link29_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound29_2_checked
theorem weight30_member : ReferenceWeightData.CoarseLowerShape.Batch0003.cert30∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound30_1_checked : cell30_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound30_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell30_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight30_member hc link30_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound30_1_checked
theorem bound30_2_checked : cell30_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound30_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell30_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight30_member hc link30_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound30_2_checked
theorem weight31_member : ReferenceWeightData.CoarseLowerShape.Batch0003.cert31∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound31_1_checked : cell31_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound31_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell31_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight31_member hc link31_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound31_1_checked
theorem bound31_2_checked : cell31_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound31_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell31_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight31_member hc link31_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound31_2_checked
theorem actual_bounds : ∀ w∈ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,∀ z∈Set.Ioc (w.cell.flow.segment.left.z:ℝ) w.cell.flow.segment.right.z,
    |force 1 z|≤100 ∧ |force 2 z|≤100 := by
  intro w hw
  simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>⟨actual_bound24_1 hz,actual_bound24_2 hz⟩
  · exact fun z hz=>⟨actual_bound25_1 hz,actual_bound25_2 hz⟩
  · exact fun z hz=>⟨actual_bound26_1 hz,actual_bound26_2 hz⟩
  · exact fun z hz=>⟨actual_bound27_1 hz,actual_bound27_2 hz⟩
  · exact fun z hz=>⟨actual_bound28_1 hz,actual_bound28_2 hz⟩
  · exact fun z hz=>⟨actual_bound29_1 hz,actual_bound29_2 hz⟩
  · exact fun z hz=>⟨actual_bound30_1 hz,actual_bound30_2 hz⟩
  · exact fun z hz=>⟨actual_bound31_1 hz,actual_bound31_2 hz⟩
end OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Batch0003

namespace OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Batch0004
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cell32_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.flow,1,⟨1795899612256212323281397792965211713631909052416,1796797256519179506982652869101144956493860175872⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-14452685472466387744396706289745531294523,14452685472466387744396706289745531294523⟩,⟨11258029279332058316403494232906436297139204487860,11308472080975476576369718843481643969678639724427⟩,⟨637208193724052733748452141235002777550045075990,649458993274230042086755652036828336489305127622⟩,⟨32868202179197288874907839443821766295887888252928,33517317670948367830707318139067958807223989174272⟩⟩
theorem link32_1_checked : cell32_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert32 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.start)/500000)=true := by decide +kernel
def cell32_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.flow,2,⟨1795899612256212323281397792965211713631909052416,1796797256519179506982652869101144956493860175872⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-14452685472466387744396706289745531294523,14452685472466387744396706289745531294523⟩,⟨11294124776153527475976222148658121159517173386531,11354034353444716826272146181299254637237542145151⟩,⟨931336515529087165406778791443036304774246856004,943398047970594591450758043986028374428785446687⟩,⟨48039806883504824256993988623281826851965003366400,48686938990980419279419713864542844757418000252928⟩⟩
theorem link32_2_checked : cell32_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert32 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.start)/500000)=true := by decide +kernel
def cell33_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.cell.flow,1,⟨1795003363835345578504780745746461662562350006272,1795900568527643154481247120993736507540050542592⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-14981736468337381866282721241794128708330,14981736468337381866282721241794128708330⟩,⟨11261614417622941251346073262263773015943725848526,11312097981919841498417651609568973261078717870804⟩,⟨637983463795807477131098064456540723769278358076,650243824432550268182175042136553989009024999205⟩,⟨32891768704920466472010903375678181820927590793216,33541074527330126483745290969279451474638223179776⟩⟩
theorem link33_1_checked : cell33_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert33 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.start)/500000)=true := by decide +kernel
def cell33_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.cell.flow,2,⟨1795003363835345578504780745746461662562350006272,1795900568527643154481247120993736507540050542592⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-14981736468337381866282721241794128708330,14981736468337381866282721241794128708330⟩,⟨11299491865158185805063928408570909231850618571180,11359453577478012044600599257030067811431221652823⟩,⟨932862177589938823855934082760352117392287904546,944937829603088014797369263398176368345152290484⟩,⟨48094489069091033717307107910783979486988126388224,48742067558509045374368666161032196073212262481920⟩⟩
theorem link33_2_checked : cell33_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert33 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.start)/500000)=true := by decide +kernel
def cell34_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.flow,1,⟨1794311352199564358813309118330333176109364936704,1795003950227070010893436723239664431805759488000⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-15390405072236065267039763534338494994041,15390405072236065267039763534338494994041⟩,⟨11270522315973624456393807196352816901531609630297,11309546129986839221026320112517678543656099018891⟩,⟨640063367497547818924863541201300874128255494289,649538907172110947260041880253955211427548985833⟩,⟨32986277919911926073248961667399944716886200025088,33487985932332449961235741320621368753644623626240⟩⟩
theorem link34_1_checked : cell34_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert34 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.start)/500000)=true := by decide +kernel
def cell34_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.flow,2,⟨1794311352199564358813309118330333176109364936704,1795003950227070010893436723239664431805759488000⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-15390405072236065267039763534338494994041,15390405072236065267039763534338494994041⟩,⟨11311064809349440651072055848692710489956008746235,11357415881125963927917892907318870942678575210160⟩,⟨935586728553198526688599223702861464617412934608,944922923005077248542874472535716316914492030614⟩,⟨48216359833409207223954852051037242878361832783872,48716964305763599474675808336460250221971366739968⟩⟩
theorem link34_2_checked : cell34_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert34 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.start)/500000)=true := by decide +kernel
def cell35_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.cell.flow,1,⟨1793619602385482653878293468479602153970812846080,1794311938622038235904012471775379196787516506112⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-15799073676134748667796805826882861279753,15799073676134748667796805826882861279753⟩,⟨11273293839883219736849693097133112341205381540504,11312342034938251779557963768345260247271751302898⟩,⟨640664485009214620046281774807104974944375993436,650145742576527337177416661266436899676210282035⟩,⟨33004527987238606447746065193626072715789821018112,33506350050482699005742381590155930171445088354304⟩⟩
theorem link35_1_checked : cell35_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert35 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.start)/500000)=true := by decide +kernel
def cell35_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.cell.flow,2,⟨1793619602385482653878293468479602153970812846080,1794311938622038235904012471775379196787516506112⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-15799073676134748667796805826882861279753,15799073676134748667796805826882861279753⟩,⟨11315228006129456161100744659217456971617479587004,11361610300485396712893844766617196665617715673663⟩,⟨936769550708919890247240305252191772856094365887,946114199064551354524668589166225635264040889027⟩,⟨48258705492859991394819068748604249893794832449536,48759577457991154320677036848766001172352205848576⟩⟩
theorem link35_2_checked : cell35_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert35 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.start)/500000)=true := by decide +kernel
def cell36_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.flow,1,⟨1792886932949073391545574238565181193056384188416,1793620256237327451759012608263846615716315791360⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-16232085288733064080151282270780569474364,16232085288733064080151282270780569474364⟩,⟨11274986758568129238905971947381963032785208179371,11316387100933008513288482361857712470837038810693⟩,⟨641003207796949604771277855118798882960516609020,651053952063838679143900630760446931511792408472⟩,⟨33008488455739887015414102310246089244629276819456,33540222037460136871864661910900502904913461772288⟩⟩
theorem link36_1_checked : cell36_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert36 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.start)/500000)=true := by decide +kernel
def cell36_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.flow,2,⟨1792886932949073391545574238565181193056384188416,1793620256237327451759012608263846615716315791360⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-16232085288733064080151282270780569474364,16232085288733064080151282270780569474364⟩,⟨11318143434753645846234536301786130722807645737603,11367320317976094706260404617671170506160970930066⟩,⟨937712079318982171050612265484052939502072781264,947621266035228907699857311579757827666738036741⟩,⟨48287527847261593566261562905010240641124773396480,48818420759482410287524728652410482666519677370368⟩⟩
theorem link36_2_checked : cell36_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert36 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.start)/500000)=true := by decide +kernel
def cell37_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.cell.flow,1,⟨1792154556917108678129709015107272461814713024512,1792887586840059780856865516445409020264906227712⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-16665096901331379492505758714678277668975,16665096901331379492505758714678277668975⟩,⟨11277921282275075464768872947284764827460690100173,11319349055799285574068102365764267190353975985089⟩,⟨641641306222267688693045083053275337838400646617,651698482926672314980879859435390259791373136423⟩,⟨33027850140902889328204726057791829169394241503232,33559712092310215066849858244181994192488238153728⟩⟩
theorem link37_1_checked : cell37_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert37 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.start)/500000)=true := by decide +kernel
def cell37_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.cell.flow,2,⟨1792154556917108678129709015107272461814713024512,1792887586840059780856865516445409020264906227712⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-16665096901331379492505758714678277668975,16665096901331379492505758714678277668975⟩,⟨11322565815723324862679494383724243021681069652034,11371777867400874189085821800712936689898839193233⟩,⟨938968030174442173898490842760342249236872043847,948886737192469466399420342667202934512751204326⟩,⟨48332451546688027437351504795471499072418202255360,48863645669614075291007588196983387229427765084160⟩⟩
theorem link37_2_checked : cell37_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert37 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.start)/500000)=true := by decide +kernel
def cell38_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.flow,1,⟨1791273584107284168899208796434223390760118517760,1792155487097041086604051699649470226350366261248⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-17186195115626682683795786180446914895066,17186195115626682683795786180446914895066⟩,⟨11276949279199240394230122229581576209675138000020,11326840358597759075615664524889823879473412402093⟩,⟨641325981974364630881422895808156874976314799711,653435515210912516813613240602548958595341240870⟩,⟨32995391338260983278574566496351136345302358818816,33635421944519994347749751701718212829403785723904⟩⟩
theorem link38_1_checked : cell38_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert38 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.start)/500000)=true := by decide +kernel
def cell38_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.flow,2,⟨1791273584107284168899208796434223390760118517760,1792155487097041086604051699649470226350366261248⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-17186195115626682683795786180446914895066,17186195115626682683795786180446914895066⟩,⟨11322452218954098500399103121552255630424852837824,11381718787985661741731497368989681818706615835997⟩,⟨939348493741191947891100481544659365393637829233,951295763003834947204071627968301458124675501473⟩,⟨48328266819246102526356648585612677361819593998336,48967697067793588809075706930713537247038647828480⟩⟩
theorem link38_2_checked : cell38_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert38 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.start)/500000)=true := by decide +kernel
def cell39_1 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.cell.flow,1,⟨1790393035322236899452507276388492972377902153728,1791274514365154021090828109693648906897137336320⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-17707293329921985875085813646215552121158,17707293329921985875085813646215552121158⟩,⟨11280475626855819181906826488185934174154520523752,11330406530161352327247697491368884026749055124884⟩,⟨642094954786641234405507322318047526416834191247,654213825262303258044046695161271739446005205476⟩,⟨33018714570487139638665056430283256843917540196352,33658931540332029605337692525157738894941954768896⟩⟩
theorem link39_1_checked : cell39_1.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert39 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.start)/500000)=true := by decide +kernel
def cell39_2 : Transport.ReferencePositionCell := ⟨ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.cell.flow,2,⟨1790393035322236899452507276388492972377902153728,1791274514365154021090828109693648906897137336320⟩,⟨34816220967519948487326557121153367497383084032,34816682122234139873882719233516411353319866368⟩,⟨-17707293329921985875085813646215552121158,17707293329921985875085813646215552121158⟩,⟨11327786563657188635139522752697443365563440447740,11387104255043200204244406546412321872143386445761⟩,⟨940862795737474163258536071385257029210381777862,952823900880052004167161586112439457365621969449⟩,⟨48382380140594506051104251152143404996172229640192,49022247964484535529967377578998328801986284093440⟩⟩
theorem link39_2_checked : cell39_2.inputLinkCheckWithError ReferenceWeightData.CoarseLowerShape.scale 1208925819614629174706176 ReferenceWeightData.CoarseLowerShape.Batch0004.cert39 ((ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.z-ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.start)/500000)=true := by decide +kernel
def cells : List Transport.ReferencePositionCell := [cell32_1,cell32_2,cell33_1,cell33_2,cell34_1,cell34_2,cell35_1,cell35_2,cell36_1,cell36_2,cell37_1,cell37_2,cell38_1,cell38_2,cell39_1,cell39_2]
theorem checked : cells.all (fun c => c.check scale 1)=true := by decide +kernel
theorem weight32_member : ReferenceWeightData.CoarseLowerShape.Batch0004.cert32∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound32_1_checked : cell32_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound32_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell32_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight32_member hc link32_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound32_1_checked
theorem bound32_2_checked : cell32_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound32_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell32_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight32_member hc link32_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound32_2_checked
theorem weight33_member : ReferenceWeightData.CoarseLowerShape.Batch0004.cert33∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound33_1_checked : cell33_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound33_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell33_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight33_member hc link33_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound33_1_checked
theorem bound33_2_checked : cell33_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound33_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell33_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight33_member hc link33_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound33_2_checked
theorem weight34_member : ReferenceWeightData.CoarseLowerShape.Batch0004.cert34∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound34_1_checked : cell34_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound34_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell34_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight34_member hc link34_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound34_1_checked
theorem bound34_2_checked : cell34_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound34_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell34_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight34_member hc link34_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound34_2_checked
theorem weight35_member : ReferenceWeightData.CoarseLowerShape.Batch0004.cert35∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound35_1_checked : cell35_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound35_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell35_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight35_member hc link35_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound35_1_checked
theorem bound35_2_checked : cell35_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound35_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell35_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight35_member hc link35_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound35_2_checked
theorem weight36_member : ReferenceWeightData.CoarseLowerShape.Batch0004.cert36∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound36_1_checked : cell36_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound36_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell36_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight36_member hc link36_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound36_1_checked
theorem bound36_2_checked : cell36_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound36_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell36_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight36_member hc link36_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound36_2_checked
theorem weight37_member : ReferenceWeightData.CoarseLowerShape.Batch0004.cert37∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound37_1_checked : cell37_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound37_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell37_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight37_member hc link37_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound37_1_checked
theorem bound37_2_checked : cell37_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound37_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell37_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight37_member hc link37_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound37_2_checked
theorem weight38_member : ReferenceWeightData.CoarseLowerShape.Batch0004.cert38∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound38_1_checked : cell38_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound38_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell38_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight38_member hc link38_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound38_1_checked
theorem bound38_2_checked : cell38_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound38_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell38_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight38_member hc link38_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound38_2_checked
theorem weight39_member : ReferenceWeightData.CoarseLowerShape.Batch0004.cert39∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,?_,?_⟩
  · simp only [List.mem_cons,List.mem_singleton]; tauto
  · simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto
theorem bound39_1_checked : cell39_1.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound39_1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.z) : |force 1 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell39_1 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight39_member hc link39_1_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound39_1_checked
theorem bound39_2_checked : cell39_2.force.maxAbs≤100*scale := by decide +kernel
theorem actual_bound39_2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.z) : |force 2 z|≤100 := by
  have hc := List.all_eq_true.mp checked cell39_2 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  have hv := actual_force weight39_member hc link39_2_checked rfl hz
  have hb := IntegerInterval.abs_bound (by norm_num [scale]) hv
  apply hb.trans
  apply (div_le_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  exact_mod_cast bound39_2_checked
theorem actual_bounds : ∀ w∈ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,∀ z∈Set.Ioc (w.cell.flow.segment.left.z:ℝ) w.cell.flow.segment.right.z,
    |force 1 z|≤100 ∧ |force 2 z|≤100 := by
  intro w hw
  simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>⟨actual_bound32_1 hz,actual_bound32_2 hz⟩
  · exact fun z hz=>⟨actual_bound33_1 hz,actual_bound33_2 hz⟩
  · exact fun z hz=>⟨actual_bound34_1 hz,actual_bound34_2 hz⟩
  · exact fun z hz=>⟨actual_bound35_1 hz,actual_bound35_2 hz⟩
  · exact fun z hz=>⟨actual_bound36_1 hz,actual_bound36_2 hz⟩
  · exact fun z hz=>⟨actual_bound37_1 hz,actual_bound37_2 hz⟩
  · exact fun z hz=>⟨actual_bound38_1 hz,actual_bound38_2 hz⟩
  · exact fun z hz=>⟨actual_bound39_1 hz,actual_bound39_2 hz⟩
end OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Batch0004
