import Nlp.Core.Data.FloatArrayExt

namespace NlpTests.Core.FloatArrayExt

private def values : FloatArray := FloatArray.replicate 3 2.5

private def updated : FloatArray :=
  values.set 1 7.0 (by simp [values])

example : (FloatArray.emptyWithCapacity 32).size = 0 := by native_decide

example : values.size = 3 := by native_decide

example : (values.push 4.0).size = 4 := by native_decide

example : (values.set! 99 4.0).size = values.size := by simp

example : (values.getD 1 9.0).toBits = (2.5 : Float).toBits := by native_decide

example : (values.getD 3 9.0).toBits = (9.0 : Float).toBits := by native_decide

example : (updated.getD 1 0.0).toBits = (7.0 : Float).toBits := by native_decide

example : updated.size = values.size := by native_decide

example : updated.get 1 (by simp [updated, values]) = 7.0 := by
  unfold updated
  apply FloatArray.get_set

example : values.set! 1 7.0 = updated := by
  unfold updated
  exact FloatArray.set!_eq_set values 1 7.0 (by simp [values])

private def uupdated : FloatArray :=
  values.uset 1 5.0 (by simp [values])

example : uupdated.uget 1 (by simp [uupdated, values]) = 5.0 := by
  unfold uupdated
  apply FloatArray.get_uset

example :
    values.uset 1 5.0 (by simp [values]) =
      values.set (1 : USize).toNat 5.0 (by simp [values]) :=
  FloatArray.uset_eq_set values 1 5.0 (by simp [values])

example : (FloatArray.ofArray #[1.0, 2.0]).size = 2 := by native_decide

end NlpTests.Core.FloatArrayExt
