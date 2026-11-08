/-!
# Charter.Core.Calendar — Exact Civil-Calendar & Epoch-Day Arithmetic (`D38`, `#48`)

Pure proleptic Gregorian calendar conversions (Howard Hinnant's exact integer algorithms)
and Catala-style month-end clamping (`AddMonths`, `AddYears`), operating over integer days
since `1970-01-01` (`0`) with zero external dependencies and zero floating-point operations.
-/

namespace Charter.Calendar

def isLeapYear (y : Int) : Bool :=
  (y % 4 == 0 && y % 100 != 0) || (y % 400 == 0)

def daysInMonth (y m : Int) : Int :=
  if m == 2 then (if isLeapYear y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30
  else 31

def validYmd (y m d : Int) : Bool :=
  m >= 1 && m <= 12 && d >= 1 && d <= daysInMonth y m

/-- Convert `(year, month 1..12, day 1..31)` to days since `1970-01-01`. -/
def daysFromCivil (y m d : Int) : Int :=
  let y' := if m <= 2 then y - 1 else y
  let era := if y' >= 0 then y' / 400 else (y' - 399) / 400
  let yoe := y' - era * 400
  let mAdj := if m > 2 then m - 3 else m + 9
  let doy := (153 * mAdj + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- Convert days since `1970-01-01` back to `(year, month 1..12, day 1..31)`. -/
def civilFromDays (z0 : Int) : Int × Int × Int :=
  let z := z0 + 719468
  let era := if z >= 0 then z / 146097 else (z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let yFinal := if m <= 2 then y + 1 else y
  (yFinal, m, d)

/-- ISO-8601 day of week: `1` = Monday .. `7` = Sunday (`1970-01-01` = Thursday = `4`). -/
def isoWeekday (days : Int) : Int :=
  let r := (days + 3) % 7
  let nonNeg := if r < 0 then r + 7 else r
  nonNeg + 1

/-- Add `deltaMonths` months to `days`, clamping day-of-month to the target month's end
(so `2026-01-31 + 1 month = 2026-02-28`, and `2024-02-29 + 120 months = 2034-02-28`). -/
def addMonthsClamped (days deltaMonths : Int) : Int :=
  let (y, m, d) := civilFromDays days
  let totalM := y * 12 + (m - 1) + deltaMonths
  let y' := Int.ediv totalM 12
  let m' := Int.emod totalM 12 + 1
  let maxD := daysInMonth y' m'
  let d' := if d <= maxD then d else maxD
  daysFromCivil y' m' d'

def addYearsClamped (days deltaYears : Int) : Int :=
  addMonthsClamped days (deltaYears * 12)

end Charter.Calendar
