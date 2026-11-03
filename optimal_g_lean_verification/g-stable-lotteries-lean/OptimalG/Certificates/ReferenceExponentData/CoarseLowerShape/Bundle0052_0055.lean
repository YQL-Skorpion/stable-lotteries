import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0048_0051
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0049_0052
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0053_0056

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0052
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert416 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0052.cert416,⟨159575347091585035009987,159575352040535657267365⟩,⟨0,1788777953088134313⟩⟩
def cert417 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0052.cert417,⟨159573558319388642442235,159573563268339264665009⟩,⟨0,1788778270318324047⟩⟩
def cert418 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0052.cert418,⟨159543439459497001140633,159543444408447458105995⟩,⟨0,30120574589592129094⟩⟩
def cert419 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0052.cert419,⟨159513320510089390169889,159513325459039681185854⟩,⟨0,30120664183963243398⟩⟩
def cert420 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0052.cert420,⟨159362193518420803846910,159362198467349200966930⟩,⟨0,151170176828201499360⟩⟩
def cert421 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0052.cert421,⟨159211064273349475049911,159211069222255539167393⟩,⟨0,151172440142948583805⟩⟩
def cert422 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0052.cert422,⟨159042928560178529077637,159042933509053074253184⟩,⟨0,168189189140081926708⟩⟩
def cert423 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0052.cert423,⟨158874790058692870802429,158874795007535224198250⟩,⟨0,168191991116529578311⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert416,cert417,cert418,cert419,cert420,cert421,cert422,cert423]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0052.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell416,ReferenceCumulativeData.CoarseLowerShapeTime.cell417,ReferenceCumulativeData.CoarseLowerShapeTime.cell418,ReferenceCumulativeData.CoarseLowerShapeTime.cell419,ReferenceCumulativeData.CoarseLowerShapeTime.cell420,ReferenceCumulativeData.CoarseLowerShapeTime.cell421,ReferenceCumulativeData.CoarseLowerShapeTime.cell422,ReferenceCumulativeData.CoarseLowerShapeTime.cell423] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0052

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0053
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert424 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0053.cert424,⟨158827231710506337700547,158827236659347977766761⟩,⟨0,47562616258000460731⟩⟩
def cert425 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0053.cert425,⟨158779673139883597134261,158779678088724519706210⟩,⟨0,47562839001850956234⟩⟩
def cert426 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0053.cert426,⟨158755347567200071851854,158755352516040898519861⟩,⟨0,24326689370048555280⟩⟩
def cert427 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0053.cert427,⟨158731021936326886978679,158731026885167617457015⟩,⟨0,24326747600881105902⟩⟩
def cert428 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0053.cert428,⟨158707523700630292980904,158707528649470936624186⟩,⟨0,23499277196701423061⟩⟩
def cert429 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0053.cert429,⟨158684025410670158412829,158684030359510714972714⟩,⟨0,23499331497316844109⟩⟩
def cert430 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0053.cert430,⟨158670678205377542928795,158670683154217148047645⟩,⟨0,13347964663172126303⟩⟩
def cert431 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0053.cert431,⟨158657330959319915387238,158657335908158568997692⟩,⟨0,13348005457682306489⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert424,cert425,cert426,cert427,cert428,cert429,cert430,cert431]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0053.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell424,ReferenceCumulativeData.CoarseLowerShapeTime.cell425,ReferenceCumulativeData.CoarseLowerShapeTime.cell426,ReferenceCumulativeData.CoarseLowerShapeTime.cell427,ReferenceCumulativeData.CoarseLowerShapeTime.cell428,ReferenceCumulativeData.CoarseLowerShapeTime.cell429,ReferenceCumulativeData.CoarseLowerShapeTime.cell430,ReferenceCumulativeData.CoarseLowerShapeTime.cell431] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0053

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0054
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert432 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0054.cert432,⟨158650528877925687631576,158650533826764215275837⟩,⟨0,6802278657367459529⟩⟩
def cert433 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0054.cert433,⟨158643726785937740487380,158643731734776142161121⟩,⟨0,6802289254992575624⟩⟩
def cert434 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0054.cert434,⟨158448057806046559998330,158448062751856965223386⟩,⟨0,195832648173584174843⟩⟩
def cert435 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0054.cert435,⟨158252380007261800756610,158252384950041206744590⟩,⟨0,195841560535956536494⟩⟩
def cert436 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0054.cert436,⟨158086359208180209921008,158086364149096706366393⟩,⟨0,166139099648381091303⟩⟩
def cert437 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0054.cert437,⟨157920331992628667177952,157920336931680681133578⟩,⟨0,166145573628275297611⟩⟩
def cert438 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0054.cert438,⟨157780904147339390900671,157780909085279926198693⟩,⟨0,139511616900956038438⟩⟩
def cert439 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0054.cert439,⟨157641471733090585924795,157641476669918851617778⟩,⟨0,139516220176687524227⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert432,cert433,cert434,cert435,cert436,cert437,cert438,cert439]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0054.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell432,ReferenceCumulativeData.CoarseLowerShapeTime.cell433,ReferenceCumulativeData.CoarseLowerShapeTime.cell434,ReferenceCumulativeData.CoarseLowerShapeTime.cell435,ReferenceCumulativeData.CoarseLowerShapeTime.cell436,ReferenceCumulativeData.CoarseLowerShapeTime.cell437,ReferenceCumulativeData.CoarseLowerShapeTime.cell438,ReferenceCumulativeData.CoarseLowerShapeTime.cell439] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0054

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0055
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert440 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0055.cert440,⟨157570948368806270095501,157570953305490853442738⟩,⟨0,70544804422592282068⟩⟩
def cert441 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0055.cert441,⟨157500423830617345591828,157500428767158194887017⟩,⟨0,70545982768734868567⟩⟩
def cert442 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0055.cert442,⟨157231595626425596405078,157231600554883099414368⟩,⟨0,269141437884443255981⟩⟩
def cert443 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0055.cert443,⟨156962750173330285192318,156962755093693285083604⟩,⟨0,269158935434025954035⟩⟩
def cert444 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0055.cert444,⟨156962509741363198118226,156962514661726198003717⟩,⟨0,240432218713083763⟩⟩
def cert445 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0055.cert445,⟨156962269309382181055102,156962274229745180934798⟩,⟨0,240432232643252007⟩⟩
def cert446 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0055.cert446,⟨156876808918043921196919,156876813838146008305137⟩,⟨0,85492171290387665559⟩⟩
def cert447 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0055.cert447,⟨156791346763677755570387,156791351683518826185380⟩,⟨0,85493942358587568729⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert440,cert441,cert442,cert443,cert444,cert445,cert446,cert447]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0055.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell440,ReferenceCumulativeData.CoarseLowerShapeTime.cell441,ReferenceCumulativeData.CoarseLowerShapeTime.cell442,ReferenceCumulativeData.CoarseLowerShapeTime.cell443,ReferenceCumulativeData.CoarseLowerShapeTime.cell444,ReferenceCumulativeData.CoarseLowerShapeTime.cell445,ReferenceCumulativeData.CoarseLowerShapeTime.cell446,ReferenceCumulativeData.CoarseLowerShapeTime.cell447] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0055
