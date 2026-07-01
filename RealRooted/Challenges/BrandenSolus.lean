import RealRooted.SymmetricDecomposition

/-!
# Brändén--Solus challenge entry point

This module exposes the current Brändén--Solus Theorem 2.6 formalization and
its main reduced target as stable names for theorem-proving sessions.
-/

noncomputable section

namespace RealRooted
namespace Challenges
namespace BrandenSolus

/-- The current nondegenerate Brändén--Solus Theorem 2.6 target. -/
abbrev theorem26Target : Prop :=
  brandenSolusTheorem26Statement

/-- The top-degree boundary case used by the reduction to Theorem 2.6. -/
abbrev theorem26TopDegreeBoundaryTarget : Prop :=
  brandenSolusTheorem26TopDegreeBoundaryStatement

/-- Challenge-facing alias for the completed Brändén--Solus Theorem 2.6. -/
theorem theorem26 :
    theorem26Target :=
  brandenSolusTheorem26

/-- Challenge-facing alias for the completed top-degree boundary case. -/
theorem theorem26TopDegreeBoundary :
    theorem26TopDegreeBoundaryTarget :=
  brandenSolusTheorem26TopDegreeBoundary

end BrandenSolus
end Challenges
end RealRooted
