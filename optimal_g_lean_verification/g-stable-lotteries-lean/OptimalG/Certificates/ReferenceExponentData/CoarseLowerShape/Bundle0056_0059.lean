import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0052_0055
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0053_0056
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0057_0060

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0056
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert448 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0056.cert448,⟨156668804271471208126901,156668809190541595603654⟩,⟨0,122607873580748747206⟩⟩
def cert449 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0056.cert449,⟨156546258139003317692464,156546263057302582295777⟩,⟨0,122611537567451537531⟩⟩
def cert450 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0056.cert450,⟨156308488281122467793958,156308493193721044288314⟩,⟨0,238017239526547802322⟩⟩
def cert451 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0056.cert451,⟨156070704564203371322937,156070709471094909753694⟩,⟨0,238031273544695363634⟩⟩
def cert452 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0056.cert452,⟨156008298367416265172080,156008303274204435080051⟩,⟨0,62423301733514253139⟩⟩
def cert453 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0056.cert453,⟨155945891206946887292226,155945896113631658393349⟩,⟨0,62424268600106652101⟩⟩
def cert454 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0056.cert454,⟨155860450018856662750790,155860454925275820984507⟩,⟨0,85473264190300228304⟩⟩
def cert455 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0056.cert455,⟨155775007018992100345240,155775011925145539097384⟩,⟨0,85475084141664995349⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert448,cert449,cert450,cert451,cert452,cert453,cert454,cert455]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0056.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell448,ReferenceCumulativeData.CoarseLowerShapeTime.cell449,ReferenceCumulativeData.CoarseLowerShapeTime.cell450,ReferenceCumulativeData.CoarseLowerShapeTime.cell451,ReferenceCumulativeData.CoarseLowerShapeTime.cell452,ReferenceCumulativeData.CoarseLowerShapeTime.cell453,ReferenceCumulativeData.CoarseLowerShapeTime.cell454,ReferenceCumulativeData.CoarseLowerShapeTime.cell455] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0056

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0057
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert456 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0057.cert456,⟨155540274983352169929108,155540279883930211407435⟩,⟨0,234975204223700898069⟩⟩
def cert457 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0057.cert457,⟨155305529138813768062795,155305534033810228123114⟩,⟨0,234989184133929508758⟩⟩
def cert458 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0057.cert458,⟨155098921820990392037146,155098926712152191932814⟩,⟨0,206796618598067183884⟩⟩
def cert459 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0057.cert459,⟨154892303669255407520714,154892308556578786295566⟩,⟨0,206807570150250613710⟩⟩
def cert460 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0057.cert460,⟨154718102294125289977880,154718107179133647443244⟩,⟨0,174336509252575732233⟩⟩
def cert461 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0057.cert461,⟨154543893133072074005578,154543898015763488357705⟩,⟨0,174344366221116099720⟩⟩
def cert462 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0057.cert462,⟨154339840400806896403933,154339845279744344194120⟩,⟨0,204238935698741371915⟩⟩
def cert463 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0057.cert463,⟨154135776870014933000633,154135781745194747296849⟩,⟨0,204249849308937317798⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert456,cert457,cert458,cert459,cert460,cert461,cert462,cert463]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0057.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell456,ReferenceCumulativeData.CoarseLowerShapeTime.cell457,ReferenceCumulativeData.CoarseLowerShapeTime.cell458,ReferenceCumulativeData.CoarseLowerShapeTime.cell459,ReferenceCumulativeData.CoarseLowerShapeTime.cell460,ReferenceCumulativeData.CoarseLowerShapeTime.cell461,ReferenceCumulativeData.CoarseLowerShapeTime.cell462,ReferenceCumulativeData.CoarseLowerShapeTime.cell463] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0057

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0058
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert464 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0058.cert464,⟨154104478240603335652533,154104483115769550703290⟩,⟨0,31303028547388503287⟩⟩
def cert465 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0058.cert465,⟨154073179354942901222810,154073184230095514985269⟩,⟨0,31303285214667293470⟩⟩
def cert466 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0058.cert466,⟨153843135635387525168736,153843140505103129651031⟩,⟨0,230281627703678218125⟩⟩
def cert467 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0058.cert467,⟨153613078000366104175610,153613082864638678374176⟩,⟨0,230295709668020436335⟩⟩
def cert468 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0058.cert468,⟨153324017705685389107375,153324022559027338631953⟩,⟨0,289438227856028727036⟩⟩
def cert469 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0058.cert469,⟨153034935109385492380679,153034939951781505541118⟩,⟨0,289460863578392194025⟩⟩
def cert470 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0058.cert470,⟨152802294902951280707680,152802299739595798154898⟩,⟨0,232886376604237970406⟩⟩
def cert471 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0058.cert471,⟨152569640038254391678399,152569644869140896298987⟩,⟨0,232901210799984369713⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert464,cert465,cert466,cert467,cert468,cert469,cert470,cert471]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0058.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell464,ReferenceCumulativeData.CoarseLowerShapeTime.cell465,ReferenceCumulativeData.CoarseLowerShapeTime.cell466,ReferenceCumulativeData.CoarseLowerShapeTime.cell467,ReferenceCumulativeData.CoarseLowerShapeTime.cell468,ReferenceCumulativeData.CoarseLowerShapeTime.cell469,ReferenceCumulativeData.CoarseLowerShapeTime.cell470,ReferenceCumulativeData.CoarseLowerShapeTime.cell471] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0058

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0059
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert472 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0059.cert472,⟨152396603209758346794223,152396608038260238243291⟩,⟨0,173173401170750308344⟩⟩
def cert473 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0059.cert473,⟨152223558175689670590192,152223563001805197053391⟩,⟨0,173181679449120219091⟩⟩
def cert474 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0059.cert474,⟨152169562091229651319557,152169566917272919102697⟩,⟨0,54009387356823781682⟩⟩
def cert475 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0059.cert475,⟨152115565204239142639445,152115570030210135196282⟩,⟨0,54010192096388458083⟩⟩
def cert476 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0059.cert476,⟨151912753718911772153732,151912758541005450452233⟩,⟨0,203000020705501625972⟩⟩
def cert477 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0059.cert477,⟨151709930813288034087057,151709935631501038688640⟩,⟨0,203011559121331163117⟩⟩
def cert478 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0059.cert478,⟨151484898531105198244383,151484903343972134407778⟩,⟨0,225265486788743462899⟩⟩
def cert479 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0059.cert479,⟨151259852021031389517989,151259856828547088067701⟩,⟨0,225279877438367980953⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert472,cert473,cert474,cert475,cert476,cert477,cert478,cert479]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0059.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell472,ReferenceCumulativeData.CoarseLowerShapeTime.cell473,ReferenceCumulativeData.CoarseLowerShapeTime.cell474,ReferenceCumulativeData.CoarseLowerShapeTime.cell475,ReferenceCumulativeData.CoarseLowerShapeTime.cell476,ReferenceCumulativeData.CoarseLowerShapeTime.cell477,ReferenceCumulativeData.CoarseLowerShapeTime.cell478,ReferenceCumulativeData.CoarseLowerShapeTime.cell479] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0059
