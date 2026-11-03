import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0060_0063
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0061_0064
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0065_0068

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0064
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert512 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0064.cert512,⟨145209561722514541322550,145209566392296396154860⟩,⟨0,162935493588762094542⟩⟩
def cert513 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0064.cert513,⟨145046747658533211222099,145046752326029452754051⟩,⟨0,162944383073577470542⟩⟩
def cert514 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0064.cert514,⟨145019771883693021271055,145019776551178911282192⟩,⟨0,26979351345836123132⟩⟩
def cert515 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0064.cert515,⟨144992795865871479661727,144992800533347017037974⟩,⟨0,26979594642722764103⟩⟩
def cert516 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0064.cert516,⟨144749584724956093841863,144749589384734548579908⟩,⟨0,243503205724231700025⟩⟩
def cert517 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0064.cert517,⟨144506353666385538180497,144506358318459361931740⟩,⟨0,243523356780633236555⟩⟩
def cert518 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0064.cert518,⟨144280506113760075694371,144280510759619767805911⟩,⟨0,226100622188888983577⟩⟩
def cert519 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0064.cert519,⟨144054641175297878776991,144054645814937746527546⟩,⟨0,226118196573858481380⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert512,cert513,cert514,cert515,cert516,cert517,cert518,cert519]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0064.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell512,ReferenceCumulativeData.CoarseLowerShapeTime.cell513,ReferenceCumulativeData.CoarseLowerShapeTime.cell514,ReferenceCumulativeData.CoarseLowerShapeTime.cell515,ReferenceCumulativeData.CoarseLowerShapeTime.cell516,ReferenceCumulativeData.CoarseLowerShapeTime.cell517,ReferenceCumulativeData.CoarseLowerShapeTime.cell518,ReferenceCumulativeData.CoarseLowerShapeTime.cell519] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0064

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0065
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert520 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0065.cert520,⟨143823473324129504450241,143823477957047742142246⟩,⟨0,231434243413335911166⟩⟩
def cert521 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0065.cert521,⟨143592287041653625980129,143592291667843890869078⟩,⟨0,231452878677120149608⟩⟩
def cert522 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0065.cert522,⟨143449036858977379470999,143449041483561194109980⟩,⟨0,143352865042882825418⟩⟩
def cert523 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0065.cert523,⟨143305779529252691927720,143305784152229114206873⟩,⟨0,143360060950357643406⟩⟩
def cert524 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0065.cert524,⟨143288459495805896564147,143288464118779489628583⟩,⟨0,17321534685136511100⟩⟩
def cert525 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0065.cert525,⟨143271139357580732861470,143271143980551496511026⟩,⟨0,17321639549831377669⟩⟩
def cert526 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0065.cert526,⟨143176280441506371048886,143176285064007754194789⟩,⟨0,94904125599327517508⟩⟩
def cert527 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0065.cert527,⟨143081418365096346673649,143081422987128166318460⟩,⟨0,94907300229702161818⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert520,cert521,cert522,cert523,cert524,cert525,cert526,cert527]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0065.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell520,ReferenceCumulativeData.CoarseLowerShapeTime.cell521,ReferenceCumulativeData.CoarseLowerShapeTime.cell522,ReferenceCumulativeData.CoarseLowerShapeTime.cell523,ReferenceCumulativeData.CoarseLowerShapeTime.cell524,ReferenceCumulativeData.CoarseLowerShapeTime.cell525,ReferenceCumulativeData.CoarseLowerShapeTime.cell526,ReferenceCumulativeData.CoarseLowerShapeTime.cell527] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0065

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0066
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert528 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0066.cert528,⟨142882877004516303573576,142882881622226437684980⟩,⟨0,198739125121165834493⟩⟩
def cert529 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0066.cert529,⟨142684321725622778305975,142684326339008038925389⟩,⟨0,198753174134268570866⟩⟩
def cert530 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0066.cert530,⟨142445197454441930021467,142445202060196089532495⟩,⟨0,239412672812714153649⟩⟩
def cert531 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0066.cert531,⟨142206052751445344778450,142206057349561565325075⟩,⟨0,239433335263365501787⟩⟩
def cert532 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0066.cert532,⟨141967750848901989598796,141967755439401013278842⟩,⟨0,238589721091692550408⟩⟩
def cert533 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0066.cert533,⟨141729428407045125935541,141729432989920103034579⟩,⟨0,238610490716427508182⟩⟩
def cert534 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0066.cert534,⟨141679519761118947579847,141679524343923825710905⟩,⟨0,49921319318905219750⟩⟩
def cert535 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0066.cert535,⟨141629610206459707160271,141629614789194473127618⟩,⟨0,49922230182087617991⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert528,cert529,cert530,cert531,cert532,cert533,cert534,cert535]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0066.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell528,ReferenceCumulativeData.CoarseLowerShapeTime.cell529,ReferenceCumulativeData.CoarseLowerShapeTime.cell530,ReferenceCumulativeData.CoarseLowerShapeTime.cell531,ReferenceCumulativeData.CoarseLowerShapeTime.cell532,ReferenceCumulativeData.CoarseLowerShapeTime.cell533,ReferenceCumulativeData.CoarseLowerShapeTime.cell534,ReferenceCumulativeData.CoarseLowerShapeTime.cell535] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0066

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0067
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert536 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0067.cert536,⟨141607502046265506827056,141607506628994184062600⟩,⟨0,22110645593517714939⟩⟩
def cert537 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0067.cert537,⟨141585393707528824041826,141585398290251412053236⟩,⟨0,22110824320936867107⟩⟩
def cert538 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0067.cert538,⟨141469966457886496966483,141469971039739558837172⟩,⟨0,115495040089032491194⟩⟩
def cert539 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0067.cert539,⟨141354534329276962769954,141354538910260129815880⟩,⟨0,115499945408156489532⟩⟩
def cert540 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0067.cert540,⟨141304481985120144471927,141304486566032536505197⟩,⟨0,50065094368731722271⟩⟩
def cert541 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0067.cert541,⟨141254428720891159485737,141254433301732763506949⟩,⟨0,50066016589736180200⟩⟩
def cert542 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0067.cert542,⟨141201760732046369105312,141201765312805123061737⟩,⟨0,52682141158442131161⟩⟩
def cert543 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0067.cert543,⟨141149091720375239847875,141149096301051127678227⟩,⟨0,52683166500317734283⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert536,cert537,cert538,cert539,cert540,cert541,cert542,cert543]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0067.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell536,ReferenceCumulativeData.CoarseLowerShapeTime.cell537,ReferenceCumulativeData.CoarseLowerShapeTime.cell538,ReferenceCumulativeData.CoarseLowerShapeTime.cell539,ReferenceCumulativeData.CoarseLowerShapeTime.cell540,ReferenceCumulativeData.CoarseLowerShapeTime.cell541,ReferenceCumulativeData.CoarseLowerShapeTime.cell542,ReferenceCumulativeData.CoarseLowerShapeTime.cell543] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0067
