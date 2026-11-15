import Tess.Validity2
namespace Tess

/-- This fuel model specifies transactional final-artifact certification. It
is not a refinement proof of the C scheduler, allocator, or proposal ordering. -/
def transaction2 (request current candidate : Certificate2) : Certificate2 :=
  if check2 request candidate then candidate else current

theorem transaction2_reject (request current candidate : Certificate2)
    (rejected : check2 request candidate=false) : transaction2 request current candidate=current := by
  simp [transaction2,rejected]

theorem transaction2_preserves (request current candidate : Certificate2)
    (valid : check2 request current=true) : check2 request (transaction2 request current candidate)=true := by
  unfold transaction2
  split <;> simp_all

def schedule2 (request : Certificate2) (propose : Nat → Certificate2 → Option Certificate2) :
    Nat → Certificate2 → Certificate2
  | 0,current => current
  | fuel+1,current =>
    let next:=match propose fuel current with
      | none => current
      | some candidate => transaction2 request current candidate
    schedule2 request propose fuel next

theorem schedule2_preserves (request : Certificate2) (propose : Nat → Certificate2 → Option Certificate2)
    (fuel : Nat) (current : Certificate2) (valid : check2 request current=true) :
    check2 request (schedule2 request propose fuel current)=true := by
  induction fuel generalizing current with
  | zero => exact valid
  | succ fuel ih =>
    simp only [schedule2]
    apply ih
    cases proposed : propose fuel current with
    | none => exact valid
    | some candidate => exact transaction2_preserves request current candidate valid

theorem schedule2_sound (request : Certificate2) (propose : Nat → Certificate2 → Option Certificate2)
    (fuel : Nat) (current : Certificate2) (valid : check2 request current=true) :
    Valid2 request (schedule2 request propose fuel current) :=
  check2_sound request _ (schedule2_preserves request propose fuel current valid)

#print axioms schedule2_sound
end Tess
