import OptimalG.Certificates.IntegerInterval

/-! A finite integer certificate covers every real point of a closed interval.
Adjacent slabs share endpoints; no floating-point geometry is trusted. -/
namespace OptimalG.Certificates

def integerSlabCoverCheck (start finish : ℤ) : List IntegerInterval → Bool
  | [] => decide (start=finish)
  | b::bs => decide (b.lo=start ∧ b.lo<b.hi) && integerSlabCoverCheck b.hi finish bs

theorem integerSlabCoverCheck_sound {start finish : ℤ} {slabs : List IntegerInterval}
    (hstrict : start<finish) (hc : integerSlabCoverCheck start finish slabs=true)
    {scale : ℕ} {x : ℝ} (hx : (⟨start,finish⟩ : IntegerInterval).Contains scale x) :
    ∃ b∈slabs,b.Contains scale x := by
  induction slabs generalizing start with
  | nil =>
    have he : start=finish := by simpa [integerSlabCoverCheck] using hc
    omega
  | cons b bs ih =>
    have hb : (b.lo=start ∧ b.lo<b.hi) ∧ integerSlabCoverCheck b.hi finish bs=true := by
      simpa only [integerSlabCoverCheck,Bool.and_eq_true_iff,decide_eq_true_eq] using hc
    by_cases hxb : (scale:ℝ)*x≤(b.hi:ℝ)
    · refine ⟨b,List.mem_cons_self,?_,hxb⟩
      change (b.lo:ℝ)≤(scale:ℝ)*x
      rw [hb.1.1]
      exact hx.1
    · have hbx : (b.hi:ℝ)<(scale:ℝ)*x := lt_of_not_ge hxb
      have hbf : b.hi<finish := by exact_mod_cast hbx.trans_le hx.2
      obtain ⟨c,hc,hcx⟩ := ih hbf hb.2 ⟨hbx.le,hx.2⟩
      exact ⟨c,List.mem_cons_of_mem b hc,hcx⟩

theorem integerSlabCoverCheck_append {start middle finish : ℤ}
    {left right : List IntegerInterval}
    (hl : integerSlabCoverCheck start middle left=true)
    (hr : integerSlabCoverCheck middle finish right=true) :
    integerSlabCoverCheck start finish (left++right)=true := by
  induction left generalizing start with
  | nil =>
    have he : start=middle := by simpa [integerSlabCoverCheck] using hl
    simpa only [List.nil_append,he] using hr
  | cons b bs ih =>
    have hb : (b.lo=start ∧ b.lo<b.hi) ∧ integerSlabCoverCheck b.hi middle bs=true := by
      simpa only [integerSlabCoverCheck,Bool.and_eq_true_iff,decide_eq_true_eq] using hl
    simpa only [List.cons_append,integerSlabCoverCheck,Bool.and_eq_true_iff,
      decide_eq_true_eq] using And.intro hb.1 (ih hb.2)

end OptimalG.Certificates
