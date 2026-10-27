module

public import RealRooted.Tactic.Attr

/-!
# Certificate attribute examples

Smoke tests for certificate attributes and their inspection command.
-/

public section

namespace RealRooted
namespace Tactic

@[rr_recurrence] theorem rr_certificates_recurrence_smoke : True := by trivial

@[rr_degree] theorem rr_certificates_degree_smoke : True := by trivial


end Tactic
end RealRooted
