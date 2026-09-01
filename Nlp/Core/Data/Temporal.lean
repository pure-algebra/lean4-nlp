import Std.Time.Date

/-!
# Exact temporal values

This module defines the calendar-independent data boundary used by temporal recognition. Civil
dates use Lean's proleptic-Gregorian `Std.Time.PlainDate`, but their constructor additionally keeps
all public values inside years 1 through 9999. No operation consults the wall clock or a time zone.
-/

namespace Nlp.Temporal

open Std.Time

/-- Largest Common Era year represented by the supported TIMEX rendering. -/
def maxYear : Nat := 9999

/-- Report invalid civil dates and calendar shifts leaving the supported year interval. -/
inductive CalendarError where
  /-- The supplied year, month, and day do not form a supported Gregorian date. -/
  | invalidDate (year month day : Nat)
  /-- A calendar shift produced a year outside 1 through `maxYear`. -/
  | unsupportedResultYear (year : Int)
  deriving Repr, DecidableEq

/-- Whether a Common Era year is a leap year in the proleptic Gregorian calendar. -/
@[inline] def isLeapYear (year : Nat) : Bool :=
  year % 4 = 0 && (year % 100 != 0 || year % 400 = 0)

/-- Number of days in a month, or zero when the month is outside 1 through 12. -/
def daysInMonth (year month : Nat) : Nat :=
  match month with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if isLeapYear year then 29 else 28
  | _ => 0

/-- A year accepted by the supported civil-date and TIMEX domains. -/
structure Year where
  private mk ::
  /-- Common Era year number. -/
  value : Nat
  /-- The year is positive. -/
  positive : 0 < value
  /-- The year fits the supported four-digit interval. -/
  bounded : value ≤ maxYear
  deriving Repr, DecidableEq

namespace Year

/-- Validate a Common Era year. -/
def ofNat? (value : Nat) : Option Year :=
  if positive : 0 < value then
    if bounded : value ≤ maxYear then some ⟨value, positive, bounded⟩ else none
  else
    none

/-- Render a supported year as exactly four ASCII digits. -/
def render (year : Year) : String :=
  let text := toString year.value
  String.ofList (List.replicate (4 - text.length) '0') ++ text

end Year

/-- A validated year and month without a day. -/
structure YearMonth where
  private mk ::
  /-- Supported Common Era year. -/
  year : Year
  /-- One-based month number. -/
  month : Nat
  /-- The month is positive. -/
  monthPositive : 0 < month
  /-- The month does not exceed December. -/
  monthBounded : month ≤ 12
  deriving Repr, DecidableEq

namespace YearMonth

/-- Validate a partial year-month value. -/
def ofNat? (year month : Nat) : Option YearMonth := do
  let year ← Year.ofNat? year
  if positive : 0 < month then
    if bounded : month ≤ 12 then some ⟨year, month, positive, bounded⟩ else none
  else
    none

/-- Render a year-month value as `YYYY-MM`. -/
def render (value : YearMonth) : String :=
  let month := toString value.month
  value.year.render ++ "-" ++ String.ofList (List.replicate (2 - month.length) '0') ++ month

end YearMonth

/-- A validated recurring month and day, permitting February 29. -/
structure MonthDay where
  private mk ::
  /-- One-based month number. -/
  month : Nat
  /-- One-based day number. -/
  day : Nat
  /-- The month is positive. -/
  monthPositive : 0 < month
  /-- The month does not exceed December. -/
  monthBounded : month ≤ 12
  /-- The day is positive. -/
  dayPositive : 0 < day
  /-- The day occurs in this month in at least one Gregorian year. -/
  dayBounded : day ≤ daysInMonth 2000 month
  deriving Repr, DecidableEq

namespace MonthDay

/-- Validate a recurring month-day value against a leap-year calendar. -/
def ofNat? (month day : Nat) : Option MonthDay :=
  if monthPositive : 0 < month then
    if monthBounded : month ≤ 12 then
      if dayPositive : 0 < day then
        if dayBounded : day ≤ daysInMonth 2000 month then
          some ⟨month, day, monthPositive, monthBounded, dayPositive, dayBounded⟩
        else
          none
      else
        none
    else
      none
  else
    none

private def padTwo (value : Nat) : String :=
  let text := toString value
  String.ofList (List.replicate (2 - text.length) '0') ++ text

/-- Render a recurring month-day as the TIMEX pattern `XXXX-MM-DD`. -/
def render (value : MonthDay) : String :=
  "XXXX-" ++ padTwo value.month ++ "-" ++ padTwo value.day

end MonthDay

/-- A validated proleptic-Gregorian date in the supported Common Era interval. -/
structure CivilDate where
  private mk ::
  /-- Validated standard-library date used for exact calendar arithmetic. -/
  plain : PlainDate
  /-- The backing year is positive. -/
  yearPositive : 0 < plain.year.toInt
  /-- The backing year remains in the supported TIMEX interval. -/
  yearBounded : plain.year.toInt ≤ maxYear
  deriving Repr, DecidableEq

namespace CivilDate

private def fromPlain (plain : PlainDate) : Except CalendarError CivilDate :=
  if positive : 0 < plain.year.toInt then
    if bounded : plain.year.toInt ≤ maxYear then
      .ok ⟨plain, positive, bounded⟩
    else
      .error (.unsupportedResultYear plain.year.toInt)
  else
    .error (.unsupportedResultYear plain.year.toInt)

/-- Validate year, month, and day and construct a supported civil date. -/
def ofYMD (year month day : Nat) : Except CalendarError CivilDate :=
  if _yearValid : 0 < year ∧ year ≤ maxYear then
    if monthValid : 0 < month ∧ month ≤ 12 then
      if dayValid : 0 < day ∧ day ≤ 31 then
        let stdYear := Year.Offset.ofNat year
        let stdMonth := Month.Ordinal.ofNat month monthValid
        let stdDay := Day.Ordinal.ofNat day dayValid
        match PlainDate.ofYearMonthDay? stdYear stdMonth stdDay with
        | some plain => fromPlain plain
        | none => .error (.invalidDate year month day)
      else
        .error (.invalidDate year month day)
    else
      .error (.invalidDate year month day)
  else
    .error (.invalidDate year month day)

/-- Validate year, month, and day, discarding the invalid-date diagnostic. -/
@[inline] def ofYMD? (year month day : Nat) : Option CivilDate :=
  (ofYMD year month day).toOption

/-- Common Era year number. -/
@[inline] def year (date : CivilDate) : Nat :=
  date.plain.year.toInt.toNat

/-- One-based month number. -/
@[inline] def month (date : CivilDate) : Nat :=
  date.plain.month.toNat

/-- One-based day number. -/
@[inline] def day (date : CivilDate) : Nat :=
  date.plain.day.val.toNat

/-- Standard-library weekday of this civil date. -/
@[inline] def weekday (date : CivilDate) : Weekday :=
  date.plain.weekday

private def padTwo (value : Nat) : String :=
  let text := toString value
  String.ofList (List.replicate (2 - text.length) '0') ++ text

/-- Render a civil date as the TIMEX value `YYYY-MM-DD`. -/
def render (date : CivilDate) : String :=
  let year := (Year.ofNat? date.year).map Year.render |>.getD (toString date.year)
  year ++ "-" ++ padTwo date.month ++ "-" ++ padTwo date.day

/-- Add an exact integral number of calendar days. -/
def addDays (date : CivilDate) (offset : Int) : Except CalendarError CivilDate :=
  fromPlain (date.plain.addDays (Day.Offset.ofInt offset))

/-- Subtract an exact integral number of calendar days. -/
@[inline] def subDays (date : CivilDate) (offset : Int) : Except CalendarError CivilDate :=
  date.addDays (-offset)

/--
Add calendar months, clipping an oversized day to the target month's final valid day.

For example, adding one month to January 31 produces February 28 or February 29.
-/
def addMonthsClip (date : CivilDate) (offset : Int) : Except CalendarError CivilDate :=
  fromPlain (date.plain.addMonthsClip (Month.Offset.ofInt offset))

/-- Subtract calendar months with the same documented end-of-month clipping policy. -/
@[inline] def subMonthsClip (date : CivilDate) (offset : Int) : Except CalendarError CivilDate :=
  date.addMonthsClip (-offset)

/--
Add calendar years, clipping February 29 to February 28 in a non-leap target year.
-/
def addYearsClip (date : CivilDate) (offset : Int) : Except CalendarError CivilDate :=
  fromPlain (date.plain.addYearsClip (Year.Offset.ofInt offset))

/-- Subtract calendar years with the same documented leap-day clipping policy. -/
@[inline] def subYearsClip (date : CivilDate) (offset : Int) : Except CalendarError CivilDate :=
  date.addYearsClip (-offset)

private def forwardDistance (source target : Weekday) : Nat :=
  (target.toNat + 7 - source.toNat) % 7

private def backwardDistance (source target : Weekday) : Nat :=
  (source.toNat + 7 - target.toNat) % 7

/-- Move to the strictly following occurrence of a weekday, one through seven days ahead. -/
def nextWeekday (date : CivilDate) (target : Weekday) : Except CalendarError CivilDate :=
  let distance := forwardDistance date.weekday target
  date.addDays (if distance = 0 then 7 else Int.ofNat distance)

/-- Move to the strictly preceding occurrence of a weekday, one through seven days behind. -/
def previousWeekday (date : CivilDate) (target : Weekday) : Except CalendarError CivilDate :=
  let distance := backwardDistance date.weekday target
  date.addDays (if distance = 0 then -7 else -Int.ofNat distance)

/--
Move to the closest occurrence of a weekday, retaining the date when it already matches.

The comparison chooses the future occurrence on a distance tie.
-/
def closestWeekday (date : CivilDate) (target : Weekday) : Except CalendarError CivilDate :=
  let future := forwardDistance date.weekday target
  let past := backwardDistance date.weekday target
  if future ≤ past then date.addDays future else date.addDays (-Int.ofNat past)

end CivilDate

/-- Precision carried by a partial calendar date. -/
inductive DatePrecision where
  | year
  | month
  | day
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- Exact absolute or recurring calendar-date values supported by the first temporal tranche. -/
inductive DateValue where
  | year (value : Year)
  | yearMonth (value : YearMonth)
  | date (value : CivilDate)
  | monthDay (value : MonthDay)
  | weekday (value : Weekday)
  deriving Repr, DecidableEq

namespace DateValue

/-- Finest calendar precision represented by a date value. -/
def precision : DateValue → DatePrecision
  | .year _ => .year
  | .yearMonth _ => .month
  | .date _ | .monthDay _ | .weekday _ => .day

/-- Render a date or recurring date pattern as a canonical TIMEX value. -/
def render : DateValue → String
  | .year value => value.render
  | .yearMonth value => value.render
  | .date value => value.render
  | .monthDay value => value.render
  | .weekday value => "XXXX-WXX-" ++ toString value.toNat

end DateValue

/-- Precision retained by a local wall-clock time. -/
inductive TimePrecision where
  | hour
  | minute
  | second
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- Well-formedness predicate for a local time and its advertised precision. -/
def ClockTime.WF (hour minute second : Nat) (precision : TimePrecision) : Prop :=
  hour < 24 ∧ minute < 60 ∧ second < 60 ∧
    match precision with
    | .hour => minute = 0 ∧ second = 0
    | .minute => second = 0
    | .second => True

/-- Clock well-formedness is decidable from its bounded natural components. -/
instance (hour minute second : Nat) (precision : TimePrecision) :
    Decidable (ClockTime.WF hour minute second precision) := by
  cases precision <;> unfold ClockTime.WF <;> infer_instance

/-- A constructor-protected local time with exact hour, minute, or second precision. -/
structure ClockTime where
  private mk ::
  /-- Zero-based hour in the local day. -/
  hour : Nat
  /-- Zero-based minute in the hour. -/
  minute : Nat
  /-- Zero-based second in the minute. -/
  second : Nat
  /-- Finest component supplied by the source expression. -/
  precision : TimePrecision
  /-- Bounds and omitted-component invariants. -/
  valid : ClockTime.WF hour minute second precision
  deriving Repr, DecidableEq

namespace ClockTime

/-- Validate all clock components and their precision relationship. -/
def ofHMS? (hour minute second : Nat) (precision : TimePrecision) : Option ClockTime :=
  if valid : ClockTime.WF hour minute second precision then
    some ⟨hour, minute, second, precision, valid⟩
  else
    none

/-- Validate a clock value carrying hour precision. -/
@[inline] def ofHour? (hour : Nat) : Option ClockTime :=
  ofHMS? hour 0 0 .hour

/-- Validate a clock value carrying minute precision. -/
@[inline] def ofHourMinute? (hour minute : Nat) : Option ClockTime :=
  ofHMS? hour minute 0 .minute

/-- Validate a clock value carrying second precision. -/
@[inline] def ofHourMinuteSecond? (hour minute second : Nat) : Option ClockTime :=
  ofHMS? hour minute second .second

private def padTwo (value : Nat) : String :=
  let text := toString value
  String.ofList (List.replicate (2 - text.length) '0') ++ text

/-- Render a local time as `THH`, `THH:MM`, or `THH:MM:SS`. -/
def render (time : ClockTime) : String :=
  match time.precision with
  | .hour => "T" ++ padTwo time.hour
  | .minute => "T" ++ padTwo time.hour ++ ":" ++ padTwo time.minute
  | .second =>
      "T" ++ padTwo time.hour ++ ":" ++ padTwo time.minute ++ ":" ++ padTwo time.second

end ClockTime

/-- A nonzero exact integral ISO-style duration split into calendar and clock components. -/
structure DurationComponents where
  private mk ::
  /-- Calendar years. -/
  years : Nat
  /-- Calendar months. -/
  months : Nat
  /-- Exact seven-day weeks. -/
  weeks : Nat
  /-- Exact calendar days. -/
  days : Nat
  /-- Exact hours. -/
  hours : Nat
  /-- Exact minutes. -/
  minutes : Nat
  /-- Exact seconds. -/
  seconds : Nat
  /-- At least one component is positive. -/
  nonzero : 0 < years + months + weeks + days + hours + minutes + seconds
  deriving Repr, DecidableEq

namespace DurationComponents

/-- Validate that an exact duration has at least one nonzero component. -/
def ofComponents? (years months weeks days hours minutes seconds : Nat) :
    Option DurationComponents :=
  if nonzero : 0 < years + months + weeks + days + hours + minutes + seconds then
    some ⟨years, months, weeks, days, hours, minutes, seconds, nonzero⟩
  else
    none

/-- Duration component named by a bounded-rendering diagnostic. -/
inductive RenderComponent where
  /-- Calendar-year component. -/
  | years
  /-- Calendar-month component. -/
  | months
  /-- Exact-week component used by a week-only rendering. -/
  | weeks
  /-- Exact-day component after folding compound weeks into days. -/
  | foldedDays
  /-- Clock-hour component. -/
  | hours
  /-- Clock-minute component. -/
  | minutes
  /-- Clock-second component. -/
  | seconds
  deriving Repr, DecidableEq, Inhabited

/-- Allocation policy for rendering duration components supplied by an external boundary. -/
structure RenderConfig where
  /-- Maximum decimal digits in any numeral that would be rendered. -/
  maxComponentDigits : Nat := 20
  /-- Maximum bytes in the final ASCII duration rendering. -/
  maxOutputBytes : Nat := 128
  deriving Repr, DecidableEq, Inhabited

/-- Why a duration failed bounded rendering before any numeral was converted to text. -/
inductive RenderError where
  /-- A rendered component needs more decimal digits than the configured limit. -/
  | componentDigitsExceeded (component : RenderComponent) (limit : Nat)
  /-- The exact ASCII output length exceeds the configured byte limit. -/
  | outputBytesExceeded (required limit : Nat)
  deriving Repr, DecidableEq

private def decimalDigitsWithin (value maxDigits : Nat) : Option Nat :=
  let rec loop (remaining digits fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        if remaining < 10 then some (digits + 1)
        else loop (remaining / 10) (digits + 1) fuel
  loop value 0 maxDigits

private def checkedDigits (component : RenderComponent) (value : Nat)
    (config : RenderConfig) : Except RenderError Nat :=
  match decimalDigitsWithin value config.maxComponentDigits with
  | some digits => .ok digits
  | none => .error (.componentDigitsExceeded component config.maxComponentDigits)

private def checkedComponentLength (component : RenderComponent) (value : Nat)
    (config : RenderConfig) : Except RenderError Nat :=
  if value = 0 then
    .ok 0
  else do
    let digits ← checkedDigits component value config
    pure (digits + 1)

private def isOnlyWeeks (duration : DurationComponents) : Bool :=
  duration.weeks != 0 && duration.years = 0 && duration.months = 0 &&
    duration.days = 0 && duration.hours = 0 && duration.minutes = 0 &&
      duration.seconds = 0

private def checkedRenderLength (duration : DurationComponents)
    (config : RenderConfig) : Except RenderError Nat := do
  if isOnlyWeeks duration then
    let digits ← checkedDigits .weeks duration.weeks config
    pure (digits + 2)
  else
    let years ← checkedComponentLength .years duration.years config
    let months ← checkedComponentLength .months duration.months config
    let foldedDays := duration.days + 7 * duration.weeks
    let days ← checkedComponentLength .foldedDays foldedDays config
    let hours ← checkedComponentLength .hours duration.hours config
    let minutes ← checkedComponentLength .minutes duration.minutes config
    let seconds ← checkedComponentLength .seconds duration.seconds config
    let dateLength := years + months + days
    let clockLength := hours + minutes + seconds
    pure (1 + dateLength + if clockLength = 0 then 0 else 1 + clockLength)

private def component (value : Nat) (suffix : String) : String :=
  if value = 0 then "" else toString value ++ suffix

private def renderTrusted (duration : DurationComponents) : String :=
  if isOnlyWeeks duration then
    "P" ++ toString duration.weeks ++ "W"
  else
    let date := component duration.years "Y" ++ component duration.months "M" ++
      component (duration.days + 7 * duration.weeks) "D"
    let clock := component duration.hours "H" ++ component duration.minutes "M" ++
      component duration.seconds "S"
    "P" ++ date ++ if clock.isEmpty then "" else "T" ++ clock

/--
Render an exact duration under decimal-digit and final-output byte limits.

All sizes are computed with bounded arithmetic traversal before any component is converted to text.
The output is ASCII, so its byte length equals the preflighted character count.
-/
def renderWith (duration : DurationComponents) (config : RenderConfig) :
    Except RenderError String := do
  let required ← checkedRenderLength duration config
  if required ≤ config.maxOutputBytes then
    .ok (renderTrusted duration)
  else
    .error (.outputBytesExceeded required config.maxOutputBytes)

/--
Render an exact duration as a canonical TIMEX/ISO duration for trusted inputs.

This convenience has no allocation budget. External parser and model inputs must use `renderWith`.
A week-only value uses `PnW`; compound weeks become seven exact days before rendering.
-/
def render (duration : DurationComponents) : String :=
  renderTrusted duration

end DurationComponents

/-- Calendar scale used by a regular recurrence pattern. -/
inductive RecurrenceUnit where
  | day
  | week
  | month
  | year
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- Anchor pattern for a recurring temporal set. -/
inductive RecurrencePattern where
  | unit (value : RecurrenceUnit)
  | weekday (value : Weekday)
  | monthDay (value : MonthDay)
  | time (value : ClockTime)
  deriving Repr, DecidableEq

namespace RecurrencePattern

/-- Render the TIMEX value identifying the recurrence's occurrence pattern. -/
def render : RecurrencePattern → String
  | .unit .day => "P1D"
  | .unit .week => "P1W"
  | .unit .month => "P1M"
  | .unit .year => "P1Y"
  | .weekday value => "XXXX-WXX-" ++ toString value.toNat
  | .monthDay value => value.render
  | .time value => value.render

end RecurrencePattern

/-- Whether a period contains only a positive number of calendar days. -/
private def DurationComponents.isWholeDayCadence (period : DurationComponents) : Bool :=
  period.days != 0 && period.years = 0 && period.months = 0 && period.weeks = 0 &&
    period.hours = 0 && period.minutes = 0 && period.seconds = 0

/-- Whether a period contains only a positive number of exact weeks. -/
private def DurationComponents.isWholeWeekCadence (period : DurationComponents) : Bool :=
  period.weeks != 0 && period.years = 0 && period.months = 0 && period.days = 0 &&
    period.hours = 0 && period.minutes = 0 && period.seconds = 0

/-- Whether a period contains only a positive number of calendar months. -/
private def DurationComponents.isWholeMonthCadence (period : DurationComponents) : Bool :=
  period.months != 0 && period.years = 0 && period.weeks = 0 && period.days = 0 &&
    period.hours = 0 && period.minutes = 0 && period.seconds = 0

/-- Whether a period contains only a positive number of calendar years. -/
private def DurationComponents.isWholeYearCadence (period : DurationComponents) : Bool :=
  period.years != 0 && period.months = 0 && period.weeks = 0 && period.days = 0 &&
    period.hours = 0 && period.minutes = 0 && period.seconds = 0

namespace TemporalSet

/-- Exact cadence compatibility required by each recurrence occurrence pattern. -/
def WF (pattern : RecurrencePattern) (periodicity : DurationComponents) : Prop :=
  (match pattern with
    | .unit .day | .time _ => periodicity.isWholeDayCadence
    | .unit .week | .weekday _ => periodicity.isWholeWeekCadence
    | .unit .month => periodicity.isWholeMonthCadence
    | .unit .year | .monthDay _ => periodicity.isWholeYearCadence) = true

/-- Cadence compatibility is decidable by its Boolean characterization. -/
instance (pattern : RecurrencePattern) (periodicity : DurationComponents) :
    Decidable (WF pattern periodicity) := by
  unfold WF
  infer_instance

end TemporalSet

/-- Why a recurrence pattern and nonzero period could not form a coherent temporal set. -/
inductive TemporalSetError where
  /-- The period is not a positive whole unit compatible with the occurrence pattern. -/
  | incompatiblePeriod (pattern : RecurrencePattern) (periodicity : DurationComponents)
  deriving Repr, DecidableEq

/-- A recurring set whose exact nonzero period is compatible with its occurrence pattern. -/
structure TemporalSet where
  private mk ::
  /-- Pattern selecting occurrences within the recurrence. -/
  pattern : RecurrencePattern
  /-- Exact period between successive recurrence frames. -/
  periodicity : DurationComponents
  /-- The period is a positive whole cadence compatible with the pattern. -/
  valid : TemporalSet.WF pattern periodicity
  deriving Repr, DecidableEq

namespace TemporalSet

/-- Validate cadence compatibility and construct an invariant-carrying recurrence. -/
def ofPatternPeriod (pattern : RecurrencePattern)
    (periodicity : DurationComponents) : Except TemporalSetError TemporalSet :=
  if valid : TemporalSet.WF pattern periodicity then
    .ok ⟨pattern, periodicity, valid⟩
  else
    .error (.incompatiblePeriod pattern periodicity)

end TemporalSet

/-- Published four-way TIMEX semantic classification. -/
inductive Kind where
  | date
  | time
  | duration
  | set
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- Exact normalized temporal values emitted by the supported algebra. -/
inductive Value where
  | date (value : DateValue)
  | time (value : ClockTime)
  | dateTime (date : CivilDate) (time : ClockTime)
  | duration (value : DurationComponents)
  | set (value : TemporalSet)
  deriving Repr, DecidableEq

/-- Canonical TIMEX value plus the optional periodicity attribute used by sets. -/
structure TimexRendering where
  /-- Four-way semantic class retained independently of the rendered text. -/
  kind : Kind
  /-- Canonical `value` field. -/
  value : String
  /-- Canonical set periodicity, absent for scalar values. -/
  periodicity : Option String := none
  deriving Repr, DecidableEq

namespace Value

/-- Four-way TIMEX semantic class of an exact normalized value. -/
def kind : Value → Kind
  | .date _ => .date
  | .time _ | .dateTime _ _ => .time
  | .duration _ => .duration
  | .set _ => .set

/-- Render a normalized value under an explicit duration-allocation policy. -/
def renderTimexWith (config : DurationComponents.RenderConfig) :
    Value → Except DurationComponents.RenderError TimexRendering
  | .date value => .ok ⟨.date, value.render, none⟩
  | .time value => .ok ⟨.time, value.render, none⟩
  | .dateTime civil clock => .ok ⟨.time, civil.render ++ clock.render, none⟩
  | .duration value => do
      let rendered ← value.renderWith config
      return ⟨.duration, rendered, none⟩
  | .set value => do
      let periodicity ← value.periodicity.renderWith config
      return ⟨.set, value.pattern.render, some periodicity⟩

/--
Deterministically render every supported normalized temporal value from trusted components.

This convenience is unbounded for duration values and set periodicities. External parser and model
inputs must first use `DurationComponents.renderWith` under an explicit allocation policy.
-/
def renderTimex : Value → TimexRendering
  | .date value => ⟨.date, value.render, none⟩
  | .time value => ⟨.time, value.render, none⟩
  | .dateTime civil clock => ⟨.time, civil.render ++ clock.render, none⟩
  | .duration value => ⟨.duration, value.render, none⟩
  | .set value => ⟨.set, value.pattern.render, some value.periodicity.render⟩

end Value

/-- Direction of a relative temporal shift. -/
inductive ShiftDirection where
  | past
  | future
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- Reference-relative selection policy for a weekday expression. -/
inductive WeekdayRelation where
  | previous
  | closest
  | next
  | bare
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- Named day offsets relative to a reference date. -/
inductive DeicticDay where
  | dayBeforeYesterday
  | yesterday
  | today
  | tomorrow
  | dayAfterTomorrow
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- A recognized temporal expression before or after reference-context resolution. -/
inductive SymbolicExpr where
  | absolute (value : Value)
  | referenceDate
  | referenceDateTime
  | deicticDay (value : DeicticDay)
  | relativeWeekday (relation : WeekdayRelation) (weekday : Weekday)
  | shift (direction : ShiftDirection) (duration : DurationComponents)
  | atTime (base : SymbolicExpr) (time : ClockTime)
  deriving Repr, DecidableEq

/-- Why a symbolic expression failed an explicit nesting-depth boundary check. -/
inductive SymbolicDepthError where
  /-- The expression is deeper than the supplied positive-node limit. -/
  | limitExceeded (limit : Nat)
  deriving Repr, DecidableEq

namespace SymbolicExpr

private def depthLoop : SymbolicExpr → Nat → Nat
  | .atTime base _, depth => depthLoop base (depth + 1)
  | _, depth => depth

/-- Measure expression depth with a tail-recursive traversal; every expression has depth one. -/
def depth (expression : SymbolicExpr) : Nat :=
  depthLoop expression 1

private def checkDepthLoop (limit : Nat) :
    SymbolicExpr → Nat → Nat → Except SymbolicDepthError Nat
  | _, 0, _ => .error (.limitExceeded limit)
  | expression, remaining + 1, depth =>
      match expression with
      | .atTime base _ => checkDepthLoop limit base remaining (depth + 1)
      | _ => .ok depth

/--
Check expression depth without traversing beyond the supplied node limit.

The tail-recursive traversal returns the exact depth when accepted and is suitable for parser and
model boundaries before recursive derived operations are used.
-/
def checkDepth (expression : SymbolicExpr) (limit : Nat) : Except SymbolicDepthError Nat :=
  checkDepthLoop limit expression limit 1

end SymbolicExpr

/-- Explicit local reference context; absent fields never consult ambient process state. -/
structure ReferenceContext where
  /-- Optional document or discourse reference date. -/
  date : Option CivilDate := none
  /-- Optional local reference time without a time zone. -/
  time : Option ClockTime := none
  deriving Repr, DecidableEq

/-- Why a recognized symbolic expression was not reduced to an exact value. -/
inductive ResolutionReason where
  | missingReferenceDate
  | missingReferenceTime
  | ambiguousBareWeekday
  | unsupportedCompoundShift
  | calendar (error : CalendarError)
  deriving Repr, DecidableEq

/-- Resolution retains the recognized expression and the exact context used to interpret it. -/
inductive Resolution where
  | resolved (expression : SymbolicExpr) (context : ReferenceContext) (value : Value)
  | symbolic (expression : SymbolicExpr) (context : ReferenceContext)
      (reason : ResolutionReason)
  deriving Repr, DecidableEq

end Nlp.Temporal
