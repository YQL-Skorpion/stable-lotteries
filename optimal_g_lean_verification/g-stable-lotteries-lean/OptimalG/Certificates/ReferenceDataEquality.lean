import OptimalG.Certificates.ReferenceScalarCertificate

/-! Computational equality for finite reference certificate records. These
instances are ordinary structural recursors, with no classical decision axiom. -/
namespace OptimalG.Certificates.Transport

deriving instance DecidableEq for ReferenceFlowCell
deriving instance DecidableEq for ReferenceScalarCell
deriving instance DecidableEq for ReferenceScalarCertificate

end OptimalG.Certificates.Transport
