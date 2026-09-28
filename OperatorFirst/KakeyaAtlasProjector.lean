import OperatorFirst.KakeyaAtlasFamily

/-! Exact rational rank-one projector for the initial g3 forcing kernel at q=2.
No numerical eigenvalue tolerance and no assumption of the claimed kernel. -/
open scoped BigOperators
namespace OperatorFirst.KakeyaAtlasProjector
abbrev Vec := Fin 7 → ℚ
def dot (x y : Vec) : ℚ := ∑ i, x i*y i
def mode : Vec := ![-1,-1,1,-1,2,-1,-2]
def project (v : Vec) : Vec := fun i => mode i * dot mode v / 13
def target (v : Vec) : ℚ := -v 0
def targetVector : Vec := ![-1,0,0,0,0,0,0]
def constraints (v : Vec) : Fin 7 → ℚ :=
  let w := KakeyaAtlasFamily.witness 2 v
  ![w 0,w 1,w 2,w 3,w 6,w 7,w 4+w 5]

theorem dot_expansion (x y : Vec) : dot x y =
    x 0*y 0 + x 1*y 1 + x 2*y 2 + x 3*y 3 + x 4*y 4 + x 5*y 5 + x 6*y 6 := by
  simp only [dot, Fin.sum_univ_succ]
  change x 0*y 0 + (x 1*y 1 + (x 2*y 2 + (x 3*y 3 + (x 4*y 4 + (x 5*y 5 + (x 6*y 6 + 0)))))) = _
  ring

theorem mode_norm_sq : dot mode mode = 13 := by
  rw [dot_expansion]
  change (-1) * (-1) + (-1) * (-1) + (1) * (1) + (-1) * (-1) + (2) * (2) + (-1) * (-1) + (-2) * (-2) = (13 : ℚ)
  norm_num

theorem target_is_dot (v : Vec) : target v = dot targetVector v := by
  rw [dot_expansion]
  change -v 0 = (-1) * (v 0) + (0) * (v 1) + (0) * (v 2) + (0) * (v 3) + (0) * (v 4) + (0) * (v 5) + (0) * (v 6)
  ring

theorem dot_mode_project (v : Vec) : dot mode (project v) = dot mode v := by
  rw [dot_expansion mode (project v)]
  change (-1) * ((-1) * dot mode v / 13) + (-1) * ((-1) * dot mode v / 13) + (1) * ((1) * dot mode v / 13) + (-1) * ((-1) * dot mode v / 13) + (2) * ((2) * dot mode v / 13) + (-1) * ((-1) * dot mode v / 13) + (-2) * ((-2) * dot mode v / 13) = dot mode v
  ring

theorem project_idempotent (v : Vec) : project (project v) = project v := by
  funext i
  change mode i * dot mode (project v) / 13 = mode i * dot mode v / 13
  rw [dot_mode_project]

theorem project_symmetric (u v : Vec) : dot u (project v) = dot (project u) v := by
  rw [dot_expansion u (project v), dot_expansion (project u) v]
  change (u 0) * ((-1) * dot mode v / 13) + (u 1) * ((-1) * dot mode v / 13) + (u 2) * ((1) * dot mode v / 13) + (u 3) * ((-1) * dot mode v / 13) + (u 4) * ((2) * dot mode v / 13) + (u 5) * ((-1) * dot mode v / 13) + (u 6) * ((-2) * dot mode v / 13) =
    ((-1) * dot mode u / 13) * (v 0) + ((-1) * dot mode u / 13) * (v 1) + ((1) * dot mode u / 13) * (v 2) + ((-1) * dot mode u / 13) * (v 3) + ((2) * dot mode u / 13) * (v 4) + ((-1) * dot mode u / 13) * (v 5) + ((-2) * dot mode u / 13) * (v 6)
  rw [dot_expansion mode v, dot_expansion mode u]
  change (u 0) * ((-1) * ((-1) * (v 0) + (-1) * (v 1) + (1) * (v 2) + (-1) * (v 3) + (2) * (v 4) + (-1) * (v 5) + (-2) * (v 6)) / 13) + (u 1) * ((-1) * ((-1) * (v 0) + (-1) * (v 1) + (1) * (v 2) + (-1) * (v 3) + (2) * (v 4) + (-1) * (v 5) + (-2) * (v 6)) / 13) + (u 2) * ((1) * ((-1) * (v 0) + (-1) * (v 1) + (1) * (v 2) + (-1) * (v 3) + (2) * (v 4) + (-1) * (v 5) + (-2) * (v 6)) / 13) + (u 3) * ((-1) * ((-1) * (v 0) + (-1) * (v 1) + (1) * (v 2) + (-1) * (v 3) + (2) * (v 4) + (-1) * (v 5) + (-2) * (v 6)) / 13) + (u 4) * ((2) * ((-1) * (v 0) + (-1) * (v 1) + (1) * (v 2) + (-1) * (v 3) + (2) * (v 4) + (-1) * (v 5) + (-2) * (v 6)) / 13) + (u 5) * ((-1) * ((-1) * (v 0) + (-1) * (v 1) + (1) * (v 2) + (-1) * (v 3) + (2) * (v 4) + (-1) * (v 5) + (-2) * (v 6)) / 13) + (u 6) * ((-2) * ((-1) * (v 0) + (-1) * (v 1) + (1) * (v 2) + (-1) * (v 3) + (2) * (v 4) + (-1) * (v 5) + (-2) * (v 6)) / 13) =
    ((-1) * ((-1) * (u 0) + (-1) * (u 1) + (1) * (u 2) + (-1) * (u 3) + (2) * (u 4) + (-1) * (u 5) + (-2) * (u 6)) / 13) * (v 0) + ((-1) * ((-1) * (u 0) + (-1) * (u 1) + (1) * (u 2) + (-1) * (u 3) + (2) * (u 4) + (-1) * (u 5) + (-2) * (u 6)) / 13) * (v 1) + ((1) * ((-1) * (u 0) + (-1) * (u 1) + (1) * (u 2) + (-1) * (u 3) + (2) * (u 4) + (-1) * (u 5) + (-2) * (u 6)) / 13) * (v 2) + ((-1) * ((-1) * (u 0) + (-1) * (u 1) + (1) * (u 2) + (-1) * (u 3) + (2) * (u 4) + (-1) * (u 5) + (-2) * (u 6)) / 13) * (v 3) + ((2) * ((-1) * (u 0) + (-1) * (u 1) + (1) * (u 2) + (-1) * (u 3) + (2) * (u 4) + (-1) * (u 5) + (-2) * (u 6)) / 13) * (v 4) + ((-1) * ((-1) * (u 0) + (-1) * (u 1) + (1) * (u 2) + (-1) * (u 3) + (2) * (u 4) + (-1) * (u 5) + (-2) * (u 6)) / 13) * (v 5) + ((-2) * ((-1) * (u 0) + (-1) * (u 1) + (1) * (u 2) + (-1) * (u 3) + (2) * (u 4) + (-1) * (u 5) + (-2) * (u 6)) / 13) * (v 6)
  ring

theorem project_mode : project mode = mode := by
  funext i
  change mode i * dot mode mode / 13 = mode i
  rw [mode_norm_sq]
  ring

theorem mode_is_kernel : constraints mode = 0 := by
  funext i
  fin_cases i
  · change ((-1 : ℚ)+(1 : ℚ))=0
    norm_num
  · change ((2 : ℚ)*(1 : ℚ)+(-2 : ℚ))=0
    norm_num
  · change ((-1 : ℚ)-(1 : ℚ)+(2 : ℚ))=0
    norm_num
  · change (-(2 : ℚ)*(1 : ℚ)+(2 : ℚ))=0
    norm_num
  · change (-(-1 : ℚ)+(-1 : ℚ))=0
    norm_num
  · change (-(-1 : ℚ)+(-1 : ℚ))=0
    norm_num
  · change ((-(-1 : ℚ))+((-1 : ℚ)))=0
    norm_num

theorem kernel_is_mode_line (v : Vec) (h : constraints v = 0) :
    v = fun i => v 2 * mode i := by
  have h0 : v 0+v 2=0 := congrFun h 0
  have h1 : 2*v 2+v 6=0 := congrFun h 1
  have h2 : v 1-v 2+v 4=0 := congrFun h 2
  have h3 : -2*v 2+v 4=0 := congrFun h 3
  have h4 : -v 1+v 5=0 := congrFun h 4
  have h5 : -v 3+v 5=0 := congrFun h 5
  have h6 : -v 0+v 3=0 := congrFun h 6
  funext i
  fin_cases i
  · change v 0 = v 2 * (-1)
    linarith
  · change v 1 = v 2 * (-1)
    linarith
  · change v 2 = v 2 * (1)
    linarith
  · change v 3 = v 2 * (-1)
    linarith
  · change v 4 = v 2 * (2)
    linarith
  · change v 5 = v 2 * (-1)
    linarith
  · change v 6 = v 2 * (-2)
    linarith

theorem projected_vector_is_kernel (v : Vec) : constraints (project v) = 0 := by
  funext i
  fin_cases i
  · change (-1) * dot mode v / 13 + (1) * dot mode v / 13 = 0
    ring
  · change 2*((1) * dot mode v / 13) + (-2) * dot mode v / 13 = 0
    ring
  · change (-1) * dot mode v / 13 - ((1) * dot mode v / 13) + (2) * dot mode v / 13 = 0
    ring
  · change -2*((1) * dot mode v / 13) + (2) * dot mode v / 13 = 0
    ring
  · change -((-1) * dot mode v / 13) + (-1) * dot mode v / 13 = 0
    ring
  · change -((-1) * dot mode v / 13) + (-1) * dot mode v / 13 = 0
    ring
  · change -((-1) * dot mode v / 13) + (-1) * dot mode v / 13 = 0
    ring

theorem projector_fixes_kernel (v : Vec) (h : constraints v = 0) : project v = v := by
  have hv := kernel_is_mode_line v h
  have hd : dot mode v = 13 * v 2 := by
    rw [dot_expansion]
    change (-1) * (v 0) + (-1) * (v 1) + (1) * (v 2) + (-1) * (v 3) + (2) * (v 4) + (-1) * (v 5) + (-2) * (v 6) = 13 * v 2
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    have h3 := congrFun hv 3
    have h4 := congrFun hv 4
    have h5 := congrFun hv 5
    have h6 := congrFun hv 6
    change v 0 = v 2 * (-1) at h0
    change v 1 = v 2 * (-1) at h1
    change v 3 = v 2 * (-1) at h3
    change v 4 = v 2 * 2 at h4
    change v 5 = v 2 * (-1) at h5
    change v 6 = v 2 * (-2) at h6
    linarith
  funext i
  change mode i * dot mode v / 13 = v i
  rw [hd]
  calc
    mode i * (13 * v 2) / 13 = v 2 * mode i := by ring
    _ = v i := (congrFun hv i).symm

theorem target_mode_nonzero : target mode = 1 := by
  change -(-1 : ℚ)=1
  norm_num

theorem projector_target_value : dot targetVector (project targetVector) = 1/13 := by
  rw [← target_is_dot]
  change -((-1) * dot mode targetVector / 13) = 1/13
  rw [dot_expansion]
  change -((-1) * ((-1) * (-1) + (-1) * (0) + (1) * (0) + (-1) * (0) + (2) * (0) + (-1) * (0) + (-2) * (0)) / 13) = (1/13 : ℚ)
  norm_num

theorem projector_target_positive : 0 < dot targetVector (project targetVector) := by
  rw [projector_target_value]
  norm_num

theorem exact_first_witness :
    KakeyaAtlasFamily.witness 2 mode = ![0,0,0,0,1,-1,0,0] := by
  funext i
  fin_cases i
  · change ((-1 : ℚ)+(1 : ℚ))=(0 : ℚ)
    norm_num
  · change ((2 : ℚ)*(1 : ℚ)+(-2 : ℚ))=(0 : ℚ)
    norm_num
  · change ((-1 : ℚ)-(1 : ℚ)+(2 : ℚ))=(0 : ℚ)
    norm_num
  · change (-(2 : ℚ)*(1 : ℚ)+(2 : ℚ))=(0 : ℚ)
    norm_num
  · change (-(-1 : ℚ))=(1 : ℚ)
    norm_num
  · change ((-1 : ℚ))=(-1 : ℚ)
    norm_num
  · change (-(-1 : ℚ)+(-1 : ℚ))=(0 : ℚ)
    norm_num
  · change (-(-1 : ℚ)+(-1 : ℚ))=(0 : ℚ)
    norm_num

theorem kernel_line_iff (v : Vec) : constraints v = 0 ↔ ∃ a : ℚ, v = fun i => a*mode i := by
  constructor
  · intro h
    exact ⟨v 2,kernel_is_mode_line v h⟩
  · rintro ⟨a,rfl⟩
    funext i
    fin_cases i
    · change a*(-1) + a*(1) = 0
      ring
    · change 2*(a*(1)) + a*(-2) = 0
      ring
    · change a*(-1) - (a*(1)) + a*(2) = 0
      ring
    · change -2*(a*(1)) + a*(2) = 0
      ring
    · change -(a*(-1)) + a*(-1) = 0
      ring
    · change -(a*(-1)) + a*(-1) = 0
      ring
    · change -(a*(-1)) + a*(-1) = 0
      ring

end OperatorFirst.KakeyaAtlasProjector

#print axioms OperatorFirst.KakeyaAtlasProjector.mode_norm_sq
#print axioms OperatorFirst.KakeyaAtlasProjector.target_is_dot
#print axioms OperatorFirst.KakeyaAtlasProjector.dot_mode_project
#print axioms OperatorFirst.KakeyaAtlasProjector.project_idempotent
#print axioms OperatorFirst.KakeyaAtlasProjector.project_symmetric
#print axioms OperatorFirst.KakeyaAtlasProjector.project_mode
#print axioms OperatorFirst.KakeyaAtlasProjector.mode_is_kernel
#print axioms OperatorFirst.KakeyaAtlasProjector.kernel_is_mode_line
#print axioms OperatorFirst.KakeyaAtlasProjector.projected_vector_is_kernel
#print axioms OperatorFirst.KakeyaAtlasProjector.projector_fixes_kernel
#print axioms OperatorFirst.KakeyaAtlasProjector.target_mode_nonzero
#print axioms OperatorFirst.KakeyaAtlasProjector.projector_target_value
#print axioms OperatorFirst.KakeyaAtlasProjector.projector_target_positive
#print axioms OperatorFirst.KakeyaAtlasProjector.exact_first_witness
#print axioms OperatorFirst.KakeyaAtlasProjector.kernel_line_iff

#print axioms OperatorFirst.KakeyaAtlasProjector.dot_expansion
