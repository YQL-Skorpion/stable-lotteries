import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0016_0019
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0017_0020
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0021_0024

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0020
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert160 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0020.cert160,⟨191487580997860536763202,191487586480007588293765⟩,⟨0,123163887902187123159⟩⟩
def cert161 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0020.cert161,⟨191364454835513780268272,191364460316905186958451⟩,⟨0,123165497365876620278⟩⟩
def cert162 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0020.cert162,⟨191293888790735056840543,191293894271984330009995⟩,⟨0,70578965315060327135⟩⟩
def cert163 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0020.cert163,⟨191223322215719511191372,191223327696826678061737⟩,⟨0,70579497321390117216⟩⟩
def cert164 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0020.cert164,⟨190960668465404067427157,190960673939172571458075⟩,⟨0,262832951934829542714⟩⟩
def cert165 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0020.cert165,⟨190698007257780173787922,190698012724215240836062⟩,⟨0,262840500701269379636⟩⟩
def cert166 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0020.cert166,⟨190420152911959292321463,190420158369718425649703⟩,⟨0,278055125595387883718⟩⟩
def cert167 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0020.cert167,⟨190142290019203081122204,190142295468292792002542⟩,⟨0,278063781058302998052⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert160,cert161,cert162,cert163,cert164,cert165,cert166,cert167]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0020.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell160,ReferenceCumulativeData.CoarseLowerShapeTime.cell161,ReferenceCumulativeData.CoarseLowerShapeTime.cell162,ReferenceCumulativeData.CoarseLowerShapeTime.cell163,ReferenceCumulativeData.CoarseLowerShapeTime.cell164,ReferenceCumulativeData.CoarseLowerShapeTime.cell165,ReferenceCumulativeData.CoarseLowerShapeTime.cell166,ReferenceCumulativeData.CoarseLowerShapeTime.cell167] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0020

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0021
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert168 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0021.cert168,⟨189957049495627058610959,189957054942152128825746⟩,⟨0,185329835132609136947⟩⟩
def cert169 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0021.cert169,⟨189771805096685373679996,189771810540647081395301⟩,⟨0,185333742707336512535⟩⟩
def cert170 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0021.cert170,⟨189529072555729202438045,189529077993923881256342⟩,⟨0,242886049093701915888⟩⟩
def cert171 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0021.cert171,⟨189286333239164745561603,189286338671596151698358⟩,⟨0,242892897318942479784⟩⟩
def cert172 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0021.cert172,⟨189065951903629492456170,189065957331751695203087⟩,⟨0,220507992940947280055⟩⟩
def cert173 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0021.cert173,⟨188845564874790698243432,188845570298606237049064⟩,⟨0,220513740692517440646⟩⟩
def cert174 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0021.cert174,⟨188598561497147086532722,188598566914901911947779⟩,⟨0,247162647936201873021⟩⟩
def cert175 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0021.cert175,⟨188351550830804384459463,188351556242502486945302⟩,⟨0,247170013453220305262⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert168,cert169,cert170,cert171,cert172,cert173,cert174,cert175]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0021.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell168,ReferenceCumulativeData.CoarseLowerShapeTime.cell169,ReferenceCumulativeData.CoarseLowerShapeTime.cell170,ReferenceCumulativeData.CoarseLowerShapeTime.cell171,ReferenceCumulativeData.CoarseLowerShapeTime.cell172,ReferenceCumulativeData.CoarseLowerShapeTime.cell173,ReferenceCumulativeData.CoarseLowerShapeTime.cell174,ReferenceCumulativeData.CoarseLowerShapeTime.cell175] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0021

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0022
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert176 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0022.cert176,⟨188073663500538588651863,188073668903616612856562⟩,⟨0,278089152885249695525⟩⟩
def cert177 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0022.cert177,⟨187795766750805883712395,187795772145270192286686⟩,⟨0,278098681991897400701⟩⟩
def cert178 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0022.cert178,⟨187579623991540952613997,187579629381957705633192⟩,⟨0,216264970612215626396⟩⟩
def cert179 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0022.cert179,⟨187363475423367019180608,187363480809738531204103⟩,⟨0,216270831206500725114⟩⟩
def cert180 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0022.cert180,⟨187178204244622928547215,187178209628449188734397⟩,⟨0,185361042308756178282⟩⟩
def cert181 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0022.cert181,⟨186992928732094385929462,186992934113376638019793⟩,⟨0,185365408694649951607⟩⟩
def cert182 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0022.cert182,⟨186977307988123634255149,186977313369404364668603⟩,⟨0,15621382897989127267⟩⟩
def cert183 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0022.cert183,⟨186961687213112024955701,186961692594391233754805⟩,⟨0,15621413958393386111⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert176,cert177,cert178,cert179,cert180,cert181,cert182,cert183]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0022.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell176,ReferenceCumulativeData.CoarseLowerShapeTime.cell177,ReferenceCumulativeData.CoarseLowerShapeTime.cell178,ReferenceCumulativeData.CoarseLowerShapeTime.cell179,ReferenceCumulativeData.CoarseLowerShapeTime.cell180,ReferenceCumulativeData.CoarseLowerShapeTime.cell181,ReferenceCumulativeData.CoarseLowerShapeTime.cell182,ReferenceCumulativeData.CoarseLowerShapeTime.cell183] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0022

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0023
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert184 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0023.cert184,⟨186730271722995285529403,186730277099318414140364⟩,⟨0,231555313490738379583⟩⟩
def cert185 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0023.cert185,⟨186498849357141107337428,186498854728511171890473⟩,⟨0,231562252858523726158⟩⟩
def cert186 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0023.cert186,⟨186220922144046012591079,186220927506839073863272⟩,⟨0,278129123344841436475⟩⟩
def cert187 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0023.cert187,⟨185942984826354761285811,185942990180577066659074⟩,⟨0,278139338420167892851⟩⟩
def cert188 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0023.cert188,⟨185819455791125483693909,185819461144596902066515⟩,⟨0,123568944110621166772⟩⟩
def cert189 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0023.cert189,⟨185695924730686755061796,185695930083407528546021⟩,⟨0,123570979030341622427⟩⟩
def cert190 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0023.cert190,⟨185417976464463068524832,185417981808625136478946⟩,⟨0,278150543727828023740⟩⟩
def cert191 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0023.cert191,⟨185140017797738571924226,185140023133348132062916⟩,⟨0,278161055097396267508⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert184,cert185,cert186,cert187,cert188,cert189,cert190,cert191]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0023.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell184,ReferenceCumulativeData.CoarseLowerShapeTime.cell185,ReferenceCumulativeData.CoarseLowerShapeTime.cell186,ReferenceCumulativeData.CoarseLowerShapeTime.cell187,ReferenceCumulativeData.CoarseLowerShapeTime.cell188,ReferenceCumulativeData.CoarseLowerShapeTime.cell189,ReferenceCumulativeData.CoarseLowerShapeTime.cell190,ReferenceCumulativeData.CoarseLowerShapeTime.cell191] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0023
