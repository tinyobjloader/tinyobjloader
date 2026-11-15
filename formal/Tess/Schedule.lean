import Tess.Validity
namespace Tess

/-- A specification of transactional certification. It is not a refinement
proof for the C optimizer or allocator. The actual C final artifact is checked
independently by `check`. -/
def transaction (request current candidate : Certificate) : Certificate :=
  if check request candidate then candidate else current

theorem transaction_reject (request current candidate : Certificate)
    (rejected : check request candidate=false) : transaction request current candidate=current := by
  simp [transaction,rejected]

theorem transaction_preserves (request current candidate : Certificate)
    (valid : check request current=true) : check request (transaction request current candidate)=true := by
  unfold transaction
  split <;> simp_all

def schedule (request : Certificate) (propose : Nat → Certificate → Option Certificate) :
    Nat → Certificate → Certificate
  | 0,current => current
  | fuel+1,current =>
    let next := match propose fuel current with
      | none => current
      | some candidate => transaction request current candidate
    schedule request propose fuel next

theorem schedule_preserves (request : Certificate) (propose : Nat → Certificate → Option Certificate)
    (fuel : Nat) (current : Certificate) (valid : check request current=true) :
    check request (schedule request propose fuel current)=true := by
  induction fuel generalizing current with
  | zero => exact valid
  | succ fuel ih =>
    simp only [schedule]
    apply ih
    cases proposed : propose fuel current with
    | none => exact valid
    | some candidate => exact transaction_preserves request current candidate valid

theorem schedule_sound (request : Certificate) (propose : Nat → Certificate → Option Certificate)
    (fuel : Nat) (current : Certificate) (valid : check request current=true) :
    Valid request (schedule request propose fuel current) :=
  check_sound request _ (schedule_preserves request propose fuel current valid)

/-- Structural recursion performs no more than the supplied number of proposal
steps, regardless of proposal acceptance. -/
def proposalCount : Nat → Nat
  | 0 => 0
  | fuel+1 => 1+proposalCount fuel

theorem proposalCount_eq_fuel (fuel : Nat) : proposalCount fuel=fuel := by
  induction fuel <;> simp_all [proposalCount,Nat.add_comm]
#print axioms schedule_sound
end Tess
