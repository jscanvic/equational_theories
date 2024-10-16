
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 2, 3], [3, 3, 2, 3], [0, 0, 2, 0], [3, 3, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 2, 3], [3, 3, 2, 3], [0, 0, 2, 0], [3, 3, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 2, 3], [3, 3, 2, 3], [0, 0, 2, 0], [3, 3, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 2, 3], [3, 3, 2, 3], [0, 0, 2, 0], [3, 3, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 329, 395, 3798, 4559] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 308, 310, 312, 313, 315, 325, 333, 335, 360, 361, 362, 365, 367, 377, 378, 384, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3256, 3259, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3308, 3315, 3318, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3457, 3459, 3462, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3511, 3518, 3521, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3660, 3662, 3664, 3665, 3667, 3668, 3675, 3678, 3684, 3685, 3687, 3714, 3721, 3722, 3724, 3725, 3748, 3751, 3758, 3759, 3761, 3864, 3865, 3868, 3870, 3871, 3878, 3880, 3881, 3888, 3890, 3917, 3918, 3924, 3927, 3928, 3951, 3954, 3955, 3961, 3964, 4066, 4067, 4068, 4071, 4073, 4074, 4081, 4083, 4084, 4091, 4093, 4120, 4121, 4127, 4130, 4131, 4154, 4157, 4158, 4164, 4167, 4268, 4270, 4272, 4273, 4275, 4276, 4283, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4381, 4382, 4383, 4386, 4388, 4398, 4399, 4405, 4408, 4433, 4435, 4436, 4443, 4445, 4472, 4473, 4479, 4482, 4583, 4584, 4585, 4588, 4590, 4591, 4598, 4599, 4605, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 2, 3], [3, 3, 2, 3], [0, 0, 2, 0], [3, 3, 2, 3]]», by decideFin!⟩
