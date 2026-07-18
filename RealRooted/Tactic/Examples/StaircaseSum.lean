import RealRooted.Tactic.StaircaseSum

open Polynomial

namespace RealRooted
namespace Tactic

example (fs : List ℝ[X]) :
    staircaseSum fs 0 = fs.sum := by
  rr_staircaseSum_zero

example (fs : List ℝ[X]) :
    staircaseSum fs fs.length = X * fs.sum := by
  rr_staircaseSum_length

example {fs : List ℝ[X]} {m : Nat}
    (hfs : IsInterlacingSeqNonneg fs)
    (hm : m < fs.length) :
    Prec (fs.get ⟨m, hm⟩) (staircaseSum fs m) := by
  rr_staircaseSum_prec using interlacing_nonneg := hfs, index_lt := hm

example {fs : List ℝ[X]} {m : Nat}
    (hfs : IsInterlacingSeqNonneg fs)
    (hm : m < fs.length) :
    (staircaseSum fs m) ≠ 0 ∧ (staircaseSum fs m).Splits := by
  rr_staircaseSum_realrooted using interlacing_nonneg := hfs, index_lt := hm

end Tactic
end RealRooted
