import OperatorFirst.KakeyaAuditControls
-- Two maps with the same range can have different kernels.
example : LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) = LinearMap.ker (LinearMap.snd ℚ ℚ ℚ) := by
  have h := OperatorFirst.KakeyaAuditControls.same_range_different_kernels.2
  simp_all
