
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 0, 1], [3, 3, 0, 2], [1, 3, 3, 2], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 0, 1], [3, 3, 0, 2], [1, 3, 3, 2], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 0, 1], [3, 3, 0, 2], [1, 3, 3, 2], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 0, 1], [3, 3, 0, 2], [1, 3, 3, 2], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2998, 3903] [24, 25, 26, 1630, 1631, 1632, 1634, 1635, 1638, 1644, 1645, 1647, 1648, 1654, 1655, 1657, 1658, 1681, 1682, 1684, 1685, 1691, 1692, 1694, 1695, 1719, 1721, 1722, 1728, 1729, 2238, 2442, 2443, 2444, 2446, 2447, 2449, 2450, 2456, 2457, 2459, 2460, 2467, 2469, 2470, 2493, 2494, 2497, 2503, 2504, 2506, 2507, 2530, 2531, 2533, 2534, 2540, 2541, 2645, 2646, 2647, 2649, 2650, 2653, 2659, 2660, 2663, 2669, 2670, 2672, 2673, 2696, 2697, 2699, 2700, 2707, 2709, 2710, 2734, 2736, 2737, 2743, 2744, 2848, 2849, 2850, 2852, 2853, 2855, 2856, 2862, 2863, 2866, 2873, 2875, 2876, 2899, 2900, 2903, 2910, 2912, 2913, 2936, 2937, 2939, 2940, 2946, 2947, 3051, 3052, 3053, 3055, 3056, 3059, 3065, 3066, 3068, 3069, 3075, 3076, 3078, 3079, 3102, 3103, 3105, 3106, 3112, 3113, 3115, 3116, 3140, 3142, 3143, 3149, 3150, 3462, 3474, 3887, 4066, 4067, 4071, 4073, 4081, 4083, 4091, 4093] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 0, 1], [3, 3, 0, 2], [1, 3, 3, 2], [0, 1, 2, 3]]», by decideFin!⟩
