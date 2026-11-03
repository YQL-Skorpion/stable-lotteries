import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0012_0015
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0013_0016
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0017_0020

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0016
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert128 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0016.cert128,⟨202424765515950889398097,202424771164491644417779⟩,⟨0,491334609813323322561⟩⟩
def cert129 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0016.cert129,⟨201933854373273211081848,201933860014555624242326⟩,⟨0,491347317786363406011⟩⟩
def cert130 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0016.cert130,⟨201457743109069921938785,201457748743749533218474⟩,⟨0,476521819595206808592⟩⟩
def cert131 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0016.cert131,⟨200981620002373914956727,200981625630461510351145⟩,⟨0,476533920113795041316⟩⟩
def cert132 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0016.cert132,⟨200399384817264745841672,200399390433316855498632⟩,⟨0,582850117786570431678⟩⟩
def cert133 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0016.cert133,⟨199817131670823964188069,199817137274864574145047⟩,⟨0,582868551916558754876⟩⟩
def cert134 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0016.cert134,⟨199287515690383345209651,199287521285417799362636⟩,⟨0,530125515894865818760⟩⟩
def cert135 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0016.cert135,⟨198757884631541274075720,198757890217585918482472⟩,⟨0,530140950700079937133⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert128,cert129,cert130,cert131,cert132,cert133,cert134,cert135]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0016.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell128,ReferenceCumulativeData.CoarseLowerShapeTime.cell129,ReferenceCumulativeData.CoarseLowerShapeTime.cell130,ReferenceCumulativeData.CoarseLowerShapeTime.cell131,ReferenceCumulativeData.CoarseLowerShapeTime.cell132,ReferenceCumulativeData.CoarseLowerShapeTime.cell133,ReferenceCumulativeData.CoarseLowerShapeTime.cell134,ReferenceCumulativeData.CoarseLowerShapeTime.cell135] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0016

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0017
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert136 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0017.cert136,⟨198280974968790832424534,198280980548294376575160⟩,⟨0,477323360881894019457⟩⟩
def cert137 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0017.cert137,⟨197804052921215848007742,197804058494188995435321⟩,⟨0,477336006307119988236⟩⟩
def cert138 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0017.cert138,⟨197462076923275586278688,197462082493850970865970⟩,⟨0,342188917279889901436⟩⟩
def cert139 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0017.cert139,⟨197120094491809111337568,197120100059989554833315⟩,⟨0,342195446982738258945⟩⟩
def cert140 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0017.cert140,⟨196984915493532927592238,196984921061565972323023⟩,⟨0,135212277588596956416⟩⟩
def cert141 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0017.cert141,⟨196849735483829394568504,196849741051715109830529⟩,⟨0,135213294947224366527⟩⟩
def cert142 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0017.cert142,⟨196261632299896357182487,196261637855608977949506⟩,⟨0,588734060582448687444⟩⟩
def cert143 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0017.cert143,⟨195673509803924878037031,195673515347489033872393⟩,⟨0,588753862328846685815⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert136,cert137,cert138,cert139,cert140,cert141,cert142,cert143]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0017.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell136,ReferenceCumulativeData.CoarseLowerShapeTime.cell137,ReferenceCumulativeData.CoarseLowerShapeTime.cell138,ReferenceCumulativeData.CoarseLowerShapeTime.cell139,ReferenceCumulativeData.CoarseLowerShapeTime.cell140,ReferenceCumulativeData.CoarseLowerShapeTime.cell141,ReferenceCumulativeData.CoarseLowerShapeTime.cell142,ReferenceCumulativeData.CoarseLowerShapeTime.cell143] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0017

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0018
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert144 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0018.cert144,⟨195147307142109573143050,195147312677006277760893⟩,⟨0,526708435725422618649⟩⟩
def cert145 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0018.cert145,⟨194621088810124978173791,194621094336369946739589⟩,⟨0,526724457215555528026⟩⟩
def cert146 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0018.cert146,⟨194423315787996351969606,194423321313785012005841⟩,⟨0,197844511730265834517⟩⟩
def cert147 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0018.cert147,⟨194225540533437013829876,194225546058769678614954⟩,⟨0,197846762820031401076⟩⟩
def cert148 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0018.cert148,⟨193945337715912468324491,193945343239948101626003⟩,⟨0,280346415408312142292⟩⟩
def cert149 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0018.cert149,⟨193665130391005357555677,193665135913745220617229⟩,⟨0,280350975882092807712⟩⟩
def cert150 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0018.cert150,⟨193240055831284531981449,193240061349502008985773⟩,⟨0,425405408382718446289⟩⟩
def cert151 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0018.cert151,⟨192814970813743238183574,192814976327444976446670⟩,⟨0,425416051861236616461⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert144,cert145,cert146,cert147,cert148,cert149,cert150,cert151]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0018.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell144,ReferenceCumulativeData.CoarseLowerShapeTime.cell145,ReferenceCumulativeData.CoarseLowerShapeTime.cell146,ReferenceCumulativeData.CoarseLowerShapeTime.cell147,ReferenceCumulativeData.CoarseLowerShapeTime.cell148,ReferenceCumulativeData.CoarseLowerShapeTime.cell149,ReferenceCumulativeData.CoarseLowerShapeTime.cell150,ReferenceCumulativeData.CoarseLowerShapeTime.cell151] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0018

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0019
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert152 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0019.cert152,⟨192793905460370274990798,192793910974071467311193⟩,⟨0,21066165973877635515⟩⟩
def cert153 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0019.cert153,⟨192772840081182321907489,192772845594882968325340⟩,⟨0,21066191811451841008⟩⟩
def cert154 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0019.cert154,⟨192723332901615141280306,192723338415266515725749⟩,⟨0,49513519759896105783⟩⟩
def cert155 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0019.cert155,⟨192673825478051998199136,192673830991654107377549⟩,⟨0,49513764363224919233⟩⟩
def cert156 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0019.cert156,⟨192395983398918980555084,192395988903796733973446⟩,⟨0,278041997234296346561⟩⟩
def cert157 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0019.cert157,⟨192118133511848781125662,192118139008008836857780⟩,⟨0,278049912780156422126⟩⟩
def cert158 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0019.cert158,⟨191864422874268074786210,191864428363797276254463⟩,⟨0,253877519046584660350⟩⟩
def cert159 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0019.cert159,⟨191610705560139118092579,191610711043042068209061⟩,⟨0,253884277707182660399⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert152,cert153,cert154,cert155,cert156,cert157,cert158,cert159]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0019.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell152,ReferenceCumulativeData.CoarseLowerShapeTime.cell153,ReferenceCumulativeData.CoarseLowerShapeTime.cell154,ReferenceCumulativeData.CoarseLowerShapeTime.cell155,ReferenceCumulativeData.CoarseLowerShapeTime.cell156,ReferenceCumulativeData.CoarseLowerShapeTime.cell157,ReferenceCumulativeData.CoarseLowerShapeTime.cell158,ReferenceCumulativeData.CoarseLowerShapeTime.cell159] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0019
