import OptimalG.Certificates.Expression
/-! Generated exact c_x/c_y certificate. All arithmetic is kernel-reduced. -/
namespace OptimalG.Certificates.GeneratedControl
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def ratioExpr : RatExpr 4 := (.add (.mul (.mul (.var 3) (.add (.add (.mul (.var 0) (.add (.const (1 / 1)) (.neg (.var 2)))) (.neg (.mul (.mul (.add (.const (1 / 1)) (.neg (.var 2))) (.add (.const (1 / 1)) (.neg (.var 2)))) (.inv (.const (2 / 1)))))) (.neg (.var 1)))) (.add (.mul (.add (.const (1 / 1)) (.neg (.var 2))) (.const (37 / 50))) (.neg (.var 0)))) (.mul (.mul (.mul (.var 2) (.add (.var 3) (.neg (.mul (.var 2) (.inv (.const (2 / 1))))))) (.add (.const (1 / 1)) (.neg (.var 2)))) (.add (.mul (.add (.mul (.var 0) (.const (2 / 1))) (.neg (.const (19 / 50)))) (.const (37 / 50))) (.neg (.add (.add (.var 2) (.const (19 / 50))) (.neg (.var 0)))))))
def domain : Fin 4 → RatInterval := ![⟨(22493 / 40000), (56233 / 100000)⟩, ⟨(28711863873 / 1306700000000), (1041027925017 / 39062500000000)⟩, ⟨(1 / 4), (9 / 25)⟩, ⟨(21267 / 100000), (313 / 1000)⟩]
def certificate : BoxCertificate 4 := (.split 2 (61 / 200) .leaf (.split 3 (52567 / 200000) (.split 2 (133 / 400) .leaf (.split 3 (95101 / 400000) (.split 2 (277 / 800) .leaf (.split 3 (180169 / 800000) (.split 2 (113 / 320) .leaf .leaf) .leaf)) .leaf)) .leaf))
/-- 8 exact rational boxes cover the full real parameter rectangle. -/
theorem checked : certificate.checkLower ratioExpr domain (0 / 1) = true := by
  decide +kernel
end OptimalG.Certificates.GeneratedControl
