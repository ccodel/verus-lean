import VerusLean.Basic

namespace VerusLean

theorem assert_39 (y : Int) (x : Int) : x = y → y = x := by sorry


theorem assert_48 (y : Int) (x : Int) : x + y = y + x := by sorry


theorem assert_66 (y : Int) (x : Int) : x + y < y + x + x := by sorry


theorem assert_75 (y : Int) (x : Int) : x * y < y / x := by sorry


theorem assert_91 (a : UInt32) : ~~~a &&& a ^^^ a = a <<< 1 ||| a >>> 1 := by sorry


-- theorem assert_99 : 1 = 1 := by sorry

theorem assert_99 : (x : Array Int) = (y : Array Int) := by sorry

-- The JSON at testJSON/serialized_fn_lean_test.json failed to generate


theorem assert_22 (y : Nat) (x : Int) : ∀ (x : Int) (y : Nat), !(x + y = x + y + 1) := by sorry


theorem assert_9 (y : Nat) (x : Int) : ∀ (x : Int) (y : Nat), x + y = y + x := by sorry

end VerusLean
