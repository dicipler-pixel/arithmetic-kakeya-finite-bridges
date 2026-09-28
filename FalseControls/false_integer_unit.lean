import OperatorFirst.KakeyaAuditControls
-- 2 has no integer inverse: a rational forcing witness need not have an integer unit.
example : (∃ z : ℤ, 2 * z = 1) := by
  have h := OperatorFirst.KakeyaAuditControls.rational_unit_without_integer_unit.2
  simp_all
