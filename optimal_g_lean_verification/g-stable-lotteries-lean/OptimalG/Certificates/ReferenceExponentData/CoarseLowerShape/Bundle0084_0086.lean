import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0080_0083
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0081_0084
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0085_0086

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0084
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert672 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0084.cert672,⟨21415228474864573578837,21415228988578037418027⟩,⟨0,898777718564255126092⟩⟩
def cert673 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0084.cert673,⟨20517448637640871381125,20517449134512546286738⟩,⟨0,898800981585802440134⟩⟩
def cert674 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0084.cert674,⟨19622376343933221775521,19622376824129459348034⟩,⟨0,896091104984410070681⟩⟩
def cert675 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0084.cert675,⟨18727282108814536320482,18727282572450372972085⟩,⟨0,896113904596762282090⟩⟩
def cert676 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0084.cert676,⟨17335725735485368695351,17335726136243127070700⟩,⟨0,1394033738958627298645⟩⟩
def cert677 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0084.cert677,⟨15944117329886943998471,15944117668444899619674⟩,⟨0,1394089026423683101652⟩⟩
def cert678 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0084.cert678,⟨15721603978510108796359,15721604316820403494731⟩,⟨0,222577009559614580382⟩⟩
def cert679 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0084.cert679,⟨15499089312924373290129,15499089650987458607162⟩,⟨0,222578337172674997529⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert672,cert673,cert674,cert675,cert676,cert677,cert678,cert679]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0084.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell672,ReferenceCumulativeData.CoarseLowerShapeTime.cell673,ReferenceCumulativeData.CoarseLowerShapeTime.cell674,ReferenceCumulativeData.CoarseLowerShapeTime.cell675,ReferenceCumulativeData.CoarseLowerShapeTime.cell676,ReferenceCumulativeData.CoarseLowerShapeTime.cell677,ReferenceCumulativeData.CoarseLowerShapeTime.cell678,ReferenceCumulativeData.CoarseLowerShapeTime.cell679] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0084

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0085
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert680 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0085.cert680,⟨14697107860279143432817,14697108186652358929286⟩,⟨0,802809335274845499530⟩⟩
def cert681 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0085.cert681,⟨13895109512224981244742,13895109826984273813883⟩,⟨0,802826858979619733466⟩⟩
def cert682 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0085.cert682,⟨12773679450355826880629,12773679733130082826707⟩,⟨0,1123057599682971208965⟩⟩
def cert683 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0085.cert683,⟨11652216876207863069608,11652217127290185521586⟩,⟨0,1123091844504970122478⟩⟩
def cert684 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0085.cert684,⟨10879940991801105897449,10879941232639683606741⟩,⟨0,773051363024235928726⟩⟩
def cert685 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0085.cert685,⟨10107649937057439287155,10107650167718954346654⟩,⟨0,773067103001205791989⟩⟩
def cert686 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0085.cert686,⟨8977167649956673131009,8977167848454153862333⟩,⟨0,1132152336711105326593⟩⟩
def cert687 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0085.cert687,⟨7846653385219514690201,7846653551861592417899⟩,⟨0,1132186115096906876666⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert680,cert681,cert682,cert683,cert684,cert685,cert686,cert687]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0085.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell680,ReferenceCumulativeData.CoarseLowerShapeTime.cell681,ReferenceCumulativeData.CoarseLowerShapeTime.cell682,ReferenceCumulativeData.CoarseLowerShapeTime.cell683,ReferenceCumulativeData.CoarseLowerShapeTime.cell684,ReferenceCumulativeData.CoarseLowerShapeTime.cell685,ReferenceCumulativeData.CoarseLowerShapeTime.cell686,ReferenceCumulativeData.CoarseLowerShapeTime.cell687] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0085

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0086
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert688 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0086.cert688,⟨6845363193189496801408,6845363337816784435946⟩,⟨0,1002607448491009233186⟩⟩
def cert689 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0086.cert689,⟨5844048375675882745456,5844048498480551728451⟩,⟨0,1002633335236697098528⟩⟩
def cert690 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0086.cert690,⟨4922779565732107228254,4922779671610512306729⟩,⟨0,922389411184151241493⟩⟩
def cert691 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0086.cert691,⟨4001490257283265404980,4001490346374560162646⟩,⟨0,922410899241224964042⟩⟩
def cert692 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0086.cert692,⟨3126651339624527540999,3126651414389440093852⟩,⟨0,875854067376448524281⟩⟩
def cert693 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0086.cert693,⟨2251794227965371215715,2251794288518126773809⟩,⟨0,875873114514441883251⟩⟩
def cert694 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0086.cert694,⟨1125911916151152311044,1125911946269424531453⟩,⟨0,1127572530187029354712⟩⟩
def cert695 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0086.cert695,⟨0,0⟩,⟨0,1127603967797412617964⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert688,cert689,cert690,cert691,cert692,cert693,cert694,cert695]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0086.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell688,ReferenceCumulativeData.CoarseLowerShapeTime.cell689,ReferenceCumulativeData.CoarseLowerShapeTime.cell690,ReferenceCumulativeData.CoarseLowerShapeTime.cell691,ReferenceCumulativeData.CoarseLowerShapeTime.cell692,ReferenceCumulativeData.CoarseLowerShapeTime.cell693,ReferenceCumulativeData.CoarseLowerShapeTime.cell694,ReferenceCumulativeData.CoarseLowerShapeTime.cell695] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0086
