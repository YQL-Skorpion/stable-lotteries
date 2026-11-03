import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0008_0011
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0009_0012
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0013_0016

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0012
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert96 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0012.cert96,⟨218576466223207570794407,218576472150965628872348⟩,⟨0,525011110098169971600⟩⟩
def cert97 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0012.cert97,⟨218051931000285572330477,218051936918523336249875⟩,⟨0,525022353691855369484⟩⟩
def cert98 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0012.cert98,⟨217579635602810989051665,217579641514121127700071⟩,⟨0,472690595452164294385⟩⟩
def cert99 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0012.cert99,⟨217107331191093197817631,217107337095486942272487⟩,⟨0,472699855408705599438⟩⟩
def cert100 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0012.cert100,⟨216529793378400170637291,216529799270168923608445⟩,⟨0,578129692735641912036⟩⟩
def cert101 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0012.cert101,⟨215952241818919587959448,215952247698088325064333⟩,⟨0,578143889670845081038⟩⟩
def cert102 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0012.cert102,⟨215426928812195452572374,215426934681916186893730⟩,⟨0,525803398519666335871⟩⟩
def cert103 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0012.cert103,⟨214901604201219415094812,214901610061509163308020⟩,⟨0,525815342034833161473⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert96,cert97,cert98,cert99,cert100,cert101,cert102,cert103]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0012.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell96,ReferenceCumulativeData.CoarseLowerShapeTime.cell97,ReferenceCumulativeData.CoarseLowerShapeTime.cell98,ReferenceCumulativeData.CoarseLowerShapeTime.cell99,ReferenceCumulativeData.CoarseLowerShapeTime.cell100,ReferenceCumulativeData.CoarseLowerShapeTime.cell101,ReferenceCumulativeData.CoarseLowerShapeTime.cell102,ReferenceCumulativeData.CoarseLowerShapeTime.cell103] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0012

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0013
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert104 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0013.cert104,⟨214533725214180395489424,214533731071244496432606⟩,⟨0,368119738706925725925⟩⟩
def cert105 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0013.cert105,⟨214165840444791220887648,214165846298633755606905⟩,⟨0,368125637683663635429⟩⟩
def cert106 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0013.cert106,⟨213587481660461429086964,213587487501789238254156⟩,⟨0,578954761655423185173⟩⟩
def cert107 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0013.cert107,⟨213009108346111619290440,213009114174949490238975⟩,⟨0,578969745787566470285⟩⟩
def cert108 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0013.cert108,⟨212377798936939186454288,212377804749577074892299⟩,⟨0,632020735990064730172⟩⟩
def cert109 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0013.cert109,⟨211746471854897102331042,211746477651369992549280⟩,⟨0,632039000650839957680⟩⟩
def cert110 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0013.cert110,⟨211378024647612589726218,211378030440890207872374⟩,⟨0,368689752464231798949⟩⟩
def cert111 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0013.cert111,⟨211009571319840118941872,211009577109926513560642⟩,⟨0,368695990687789423590⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert104,cert105,cert106,cert107,cert108,cert109,cert110,cert111]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0013.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell104,ReferenceCumulativeData.CoarseLowerShapeTime.cell105,ReferenceCumulativeData.CoarseLowerShapeTime.cell106,ReferenceCumulativeData.CoarseLowerShapeTime.cell107,ReferenceCumulativeData.CoarseLowerShapeTime.cell108,ReferenceCumulativeData.CoarseLowerShapeTime.cell109,ReferenceCumulativeData.CoarseLowerShapeTime.cell110,ReferenceCumulativeData.CoarseLowerShapeTime.cell111] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0013

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0014
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert112 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0014.cert112,⟨210535657051302470093276,210535662834605610916525⟩,⟨0,474316057492121746441⟩⟩
def cert113 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0014.cert113,⟨210061732516868773082414,210061738293399690977402⟩,⟨0,474326574329959902487⟩⟩
def cert114 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0014.cert114,⟨209429501055927045602741,209429506816398981418475⟩,⟨0,632947753938491664551⟩⟩
def cert115 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0014.cert115,⟨208797250999131638580716,208797256743579316261283⟩,⟨0,632966946876682578126⟩⟩
def cert116 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0014.cert116,⟨208322812690093453211110,208322818427802437396372⟩,⟨0,474842206161056547526⟩⟩
def cert117 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0014.cert117,⟨207848363727119008127236,207848369458100268680585⟩,⟨0,474853112729303561346⟩⟩
def cert118 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0014.cert118,⟨207373698396741898789745,207373704121003464204335⟩,⟨0,475070137362774563030⟩⟩
def cert119 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0014.cert119,⟨206899022246737476337565,206899027964290290575626⟩,⟨0,475081210354221031885⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert112,cert113,cert114,cert115,cert116,cert117,cert118,cert119]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0014.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell112,ReferenceCumulativeData.CoarseLowerShapeTime.cell113,ReferenceCumulativeData.CoarseLowerShapeTime.cell114,ReferenceCumulativeData.CoarseLowerShapeTime.cell115,ReferenceCumulativeData.CoarseLowerShapeTime.cell116,ReferenceCumulativeData.CoarseLowerShapeTime.cell117,ReferenceCumulativeData.CoarseLowerShapeTime.cell118,ReferenceCumulativeData.CoarseLowerShapeTime.cell119] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0014

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0015
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert120 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0015.cert120,⟨206371348914904773503262,206371354623260834907255⟩,⟨0,528174315226381437974⟩⟩
def cert121 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0015.cert121,⟨205843662010072980468888,205843667709248920971299⟩,⟨0,528188236894301871971⟩⟩
def cert122 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0015.cert122,⟨205368512520812404195292,205368518213308562831809⟩,⟨0,475556229618303852117⟩⟩
def cert123 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0015.cert123,⟨204893351863324720989189,204893357549151987520451⟩,⟨0,475567652770425067072⟩⟩
def cert124 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0015.cert124,⟨204417970755755982828030,204417976434922282899835⟩,⟨0,475788769809954741097⟩⟩
def cert125 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0015.cert125,⟨203942578315395264550618,203942583987911462466954⟩,⟨0,475800358273770518375⟩⟩
def cert126 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0015.cert126,⟨203429127977272662701388,203429133641429073479455⟩,⟨0,513926566314114938124⟩⟩
def cert127 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0015.cert127,⟨202915664233068634516804,202915669888879973022407⟩,⟨0,513940295067518174294⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert120,cert121,cert122,cert123,cert124,cert125,cert126,cert127]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0015.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell120,ReferenceCumulativeData.CoarseLowerShapeTime.cell121,ReferenceCumulativeData.CoarseLowerShapeTime.cell122,ReferenceCumulativeData.CoarseLowerShapeTime.cell123,ReferenceCumulativeData.CoarseLowerShapeTime.cell124,ReferenceCumulativeData.CoarseLowerShapeTime.cell125,ReferenceCumulativeData.CoarseLowerShapeTime.cell126,ReferenceCumulativeData.CoarseLowerShapeTime.cell127] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0015
