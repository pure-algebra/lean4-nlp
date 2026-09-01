import Nlp.Core.Data.Temporal

/-! # Exact temporal data and Gregorian calendar tests -/

namespace NlpTests.Core.Temporal

open Nlp.Temporal
open Std.Time

/-- Independently state the Gregorian leap-year rule without calling production code. -/
private def oracleLeapYear (year : Nat) : Bool :=
  if year % 400 = 0 then true
  else if year % 100 = 0 then false
  else year % 4 = 0

/-- Independently calculate one Gregorian month length. -/
private def oracleDaysInMonth (year month : Nat) : Nat :=
  match month with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if oracleLeapYear year then 29 else 28
  | _ => 0

/-- Independent validity predicate used by the exhaustive constructor oracle. -/
private def oracleValidDate (year month day : Nat) : Bool :=
  0 < year && year ≤ maxYear && 0 < month && month ≤ 12 &&
    0 < day && day ≤ oracleDaysInMonth year month

/-- Compare a checked date with three expected public projections. -/
private def isDate (result : Except CalendarError CivilDate)
    (year month day : Nat) : Bool :=
  match result with
  | .ok date => date.year = year && date.month = month && date.day = day
  | .error _ => false

/-- Compare an optional checked date with three expected public projections. -/
private def isSomeDate (result : Option CivilDate) (year month day : Nat) : Bool :=
  match result with
  | some date => date.year = year && date.month = month && date.day = day
  | none => false

/-- Recognize the exact supported-year failure from a checked calendar operation. -/
private def isUnsupportedYear (result : Except CalendarError CivilDate) (year : Int) : Bool :=
  match result with
  | .error (.unsupportedResultYear actual) => actual == year
  | _ => false

/-- Compare a successful bounded duration rendering with its expected ASCII text. -/
private def isRenderOk (result : Except DurationComponents.RenderError String)
    (expected : String) : Bool :=
  match result with
  | .ok actual => actual == expected
  | .error _ => false

/-- Compare a bounded duration-rendering failure with its exact typed diagnostic. -/
private def isRenderError (result : Except DurationComponents.RenderError String)
    (expected : DurationComponents.RenderError) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

/-- Compare a successful bounded TIMEX rendering with its exact structured value. -/
private def isTimexRenderOk
    (result : Except DurationComponents.RenderError TimexRendering)
    (expected : TimexRendering) : Bool :=
  match result with
  | .ok actual => decide (actual = expected)
  | .error _ => false

/-- Compare a bounded TIMEX-rendering failure with its exact typed diagnostic. -/
private def isTimexRenderError
    (result : Except DurationComponents.RenderError TimexRendering)
    (expected : DurationComponents.RenderError) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

/-- Compare a checked recurrence failure with its exact typed diagnostic. -/
private def isTemporalSetError (result : Except TemporalSetError TemporalSet)
    (expected : TemporalSetError) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

/-- Compare a successful symbolic depth check with its expected exact depth. -/
private def isDepthOk (result : Except SymbolicDepthError Nat) (expected : Nat) : Bool :=
  match result with
  | .ok actual => actual == expected
  | .error _ => false

/-- Compare a symbolic depth failure with its exact limit diagnostic. -/
private def isDepthError (result : Except SymbolicDepthError Nat)
    (expected : SymbolicDepthError) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

/- Century and 400-year boundaries obey the proleptic-Gregorian leap rule. -/
#guard !isLeapYear 1900
#guard isLeapYear 2000
#guard !isLeapYear 2100
#guard isLeapYear 2400
#guard daysInMonth 2000 2 == 29
#guard daysInMonth 1900 2 == 28
#guard daysInMonth 2024 0 == 0
#guard daysInMonth 2024 13 == 0

/- Supported endpoint dates are constructible and expose exact components. -/
#guard isSomeDate (CivilDate.ofYMD? 1 1 1) 1 1 1
#guard isSomeDate (CivilDate.ofYMD? 9999 12 31) 9999 12 31

/- Invalid years, months, days, and non-leap February 29 are rejected. -/
#guard (CivilDate.ofYMD? 0 1 1).isNone
#guard (CivilDate.ofYMD? 10000 1 1).isNone
#guard (CivilDate.ofYMD? 2024 0 1).isNone
#guard (CivilDate.ofYMD? 2024 13 1).isNone
#guard (CivilDate.ofYMD? 2024 1 0).isNone
#guard (CivilDate.ofYMD? 2024 4 31).isNone
#guard (CivilDate.ofYMD? 1900 2 29).isNone
#guard (CivilDate.ofYMD? 2000 2 29).isSome

/- Invalid construction retains the original components in its diagnostic. -/
#guard match CivilDate.ofYMD 1900 2 29 with
  | .error (.invalidDate 1900 2 29) => true
  | _ => false

/- Exact day shifts cross leap-day, month, and year boundaries. -/
#guard match CivilDate.ofYMD? 2024 2 28 with
  | some date => isDate (date.addDays 1) 2024 2 29 && isDate (date.addDays 2) 2024 3 1
  | none => false

#guard match CivilDate.ofYMD? 1900 2 28 with
  | some date => isDate (date.addDays 1) 1900 3 1
  | none => false

#guard match CivilDate.ofYMD? 2023 12 31 with
  | some date => isDate (date.addDays 1) 2024 1 1
  | none => false

#guard match CivilDate.ofYMD? 2024 1 1 with
  | some date => isDate (date.subDays 1) 2023 12 31
  | none => false

/- Shifts leaving the supported four-digit year interval fail explicitly. -/
#guard match CivilDate.ofYMD? 1 1 1 with
  | some date =>
      match date.subDays 1 with
      | .error (.unsupportedResultYear 0) => true
      | _ => false
  | none => false

#guard match CivilDate.ofYMD? 9999 12 31 with
  | some date =>
      match date.addDays 1 with
      | .error (.unsupportedResultYear 10000) => true
      | _ => false
  | none => false

/- Month shifts use documented end-of-month clipping. -/
#guard match CivilDate.ofYMD? 2024 1 31 with
  | some date => isDate (date.addMonthsClip 1) 2024 2 29
  | none => false

#guard match CivilDate.ofYMD? 2023 1 31 with
  | some date => isDate (date.addMonthsClip 1) 2023 2 28
  | none => false

#guard match CivilDate.ofYMD? 2024 3 31 with
  | some date => isDate (date.subMonthsClip 1) 2024 2 29
  | none => false

/- Signed and multi-month shifts cross both directions of the January/December boundary. -/
#guard match CivilDate.ofYMD? 2024 1 31 with
  | some date => isDate (date.addMonthsClip (-1)) 2023 12 31
  | none => false

#guard match CivilDate.ofYMD? 2023 12 31 with
  | some date => isDate (date.addMonthsClip 2) 2024 2 29
  | none => false

#guard match CivilDate.ofYMD? 2024 3 31 with
  | some date => isDate (date.subMonthsClip 13) 2023 2 28
  | none => false

#guard match CivilDate.ofYMD? 2023 11 30 with
  | some date => isDate (date.subMonthsClip (-2)) 2024 1 30
  | none => false

/- Year shifts clip leap day only when the target year requires it. -/
#guard match CivilDate.ofYMD? 2024 2 29 with
  | some date =>
      isDate (date.addYearsClip 1) 2025 2 28 &&
        isDate (date.addYearsClip 4) 2028 2 29
  | none => false

/- Signed, multi-year, and subtraction wrappers retain leap-day clipping semantics. -/
#guard match CivilDate.ofYMD? 2024 2 29 with
  | some date =>
      isDate (date.addYearsClip (-1)) 2023 2 28 &&
        isDate (date.subYearsClip 4) 2020 2 29 &&
        isDate (date.subYearsClip (-4)) 2028 2 29 &&
        isDate (date.addYearsClip 400) 2424 2 29
  | none => false

/- Month and year shifts reject both supported-domain endpoint crossings. -/
#guard match CivilDate.ofYMD? 1 1 31 with
  | some date =>
      isUnsupportedYear (date.subMonthsClip 1) 0 &&
        isUnsupportedYear (date.addYearsClip (-1)) 0
  | none => false

#guard match CivilDate.ofYMD? 9999 12 31 with
  | some date =>
      isUnsupportedYear (date.addMonthsClip 1) 10000 &&
        isUnsupportedYear (date.subYearsClip (-1)) 10000
  | none => false

/- Published SUTime-style weekday reference cases resolve with strict or closest semantics. -/
#guard match CivilDate.ofYMD? 2011 9 19 with
  | some monday =>
      isDate (monday.previousWeekday .friday) 2011 9 16 &&
        isDate (monday.nextWeekday .friday) 2011 9 23 &&
        isDate (monday.closestWeekday .wednesday) 2011 9 21 &&
        isDate (monday.closestWeekday .monday) 2011 9 19 &&
        isDate (monday.nextWeekday .monday) 2011 9 26 &&
        isDate (monday.previousWeekday .monday) 2011 9 12
  | none => false

/- Canonical date renderings preserve partial-date precision. -/
#guard (Year.ofNat? 1).map Year.render == some "0001"
#guard (Year.ofNat? 9999).map Year.render == some "9999"
#guard (Year.ofNat? 0).isNone
#guard (Year.ofNat? 10000).isNone
#guard (YearMonth.ofNat? 1963 10).map YearMonth.render == some "1963-10"
#guard (YearMonth.ofNat? 1963 13).isNone
#guard (MonthDay.ofNat? 2 29).map MonthDay.render == some "XXXX-02-29"
#guard (MonthDay.ofNat? 2 30).isNone

#guard match CivilDate.ofYMD? 1963 10 4 with
  | some date =>
      date.render == "1963-10-04" &&
        (Value.date (.date date)).kind == .date &&
        (Value.date (.date date)).renderTimex == ⟨.date, "1963-10-04", none⟩
  | none => false

/- Clock constructors reject bounds and precision/component inconsistencies. -/
#guard (ClockTime.ofHour? 23).isSome
#guard (ClockTime.ofHour? 24).isNone
#guard (ClockTime.ofHourMinute? 12 59).isSome
#guard (ClockTime.ofHourMinute? 12 60).isNone
#guard (ClockTime.ofHourMinuteSecond? 12 34 59).isSome
#guard (ClockTime.ofHourMinuteSecond? 12 34 60).isNone
#guard (ClockTime.ofHMS? 12 1 0 .hour).isNone
#guard (ClockTime.ofHMS? 12 1 1 .minute).isNone

/- Clock rendering retains exactly the advertised source precision. -/
#guard (ClockTime.ofHour? 4).map ClockTime.render == some "T04"
#guard (ClockTime.ofHourMinute? 4 5).map ClockTime.render == some "T04:05"
#guard (ClockTime.ofHourMinuteSecond? 4 5 6).map ClockTime.render ==
  some "T04:05:06"

/- Zero duration is unrepresentable; exact components have canonical ISO/TIMEX renderings. -/
#guard (DurationComponents.ofComponents? 0 0 0 0 0 0 0).isNone
#guard (DurationComponents.ofComponents? 0 0 3 0 0 0 0).map
  DurationComponents.render == some "P3W"
#guard (DurationComponents.ofComponents? 1 2 1 3 4 5 6).map
  DurationComponents.render == some "P1Y2M10DT4H5M6S"
#guard (DurationComponents.ofComponents? 0 0 0 0 4 0 0).map
  DurationComponents.render == some "PT4H"

/- Bounded rendering accepts exact budgets and rejects either budget one unit short. -/
#guard match DurationComponents.ofComponents? 1 2 1 3 4 5 6 with
  | some duration =>
      isRenderOk
        (duration.renderWith { maxComponentDigits := 2, maxOutputBytes := 15 })
        "P1Y2M10DT4H5M6S" &&
      isRenderError
        (duration.renderWith { maxComponentDigits := 1, maxOutputBytes := 15 })
        (.componentDigitsExceeded .foldedDays 1) &&
      isRenderError
        (duration.renderWith { maxComponentDigits := 2, maxOutputBytes := 14 })
        (.outputBytesExceeded 15 14)
  | none => false

/- Week-only bounded rendering applies the numeral budget before allocating output text. -/
#guard match DurationComponents.ofComponents? 0 0 3 0 0 0 0 with
  | some duration =>
      isRenderOk
        (duration.renderWith { maxComponentDigits := 1, maxOutputBytes := 3 }) "P3W" &&
      isRenderError
        (duration.renderWith { maxComponentDigits := 0, maxOutputBytes := 3 })
        (.componentDigitsExceeded .weeks 0) &&
      isRenderError
        (duration.renderWith { maxComponentDigits := 1, maxOutputBytes := 2 })
        (.outputBytesExceeded 3 2)
  | none => false

/- Duration values retain their published TIMEX class alongside rendering. -/
#guard match DurationComponents.ofComponents? 0 0 0 3 0 0 0 with
  | some duration =>
      (Value.duration duration).kind == .duration &&
        (Value.duration duration).renderTimex == ⟨.duration, "P3D", none⟩ &&
        isTimexRenderOk
          ((Value.duration duration).renderTimexWith
            { maxComponentDigits := 1, maxOutputBytes := 3 })
          ⟨.duration, "P3D", none⟩ &&
        isTimexRenderError
          ((Value.duration duration).renderTimexWith
            { maxComponentDigits := 1, maxOutputBytes := 2 })
          (.outputBytesExceeded 3 2)
  | none => false

/- Sets render their occurrence pattern and exact periodicity separately. -/
#guard match DurationComponents.ofComponents? 0 0 3 0 0 0 0 with
  | some period =>
      match TemporalSet.ofPatternPeriod (.weekday .sunday) period with
      | .ok set =>
          (Value.set set).kind == .set &&
            (Value.set set).renderTimex == ⟨.set, "XXXX-WXX-7", some "P3W"⟩ &&
            isTimexRenderOk
              ((Value.set set).renderTimexWith
                { maxComponentDigits := 1, maxOutputBytes := 3 })
              ⟨.set, "XXXX-WXX-7", some "P3W"⟩
      | .error _ => false
  | none => false

/- Recurrence construction rejects periods expressed in an incompatible calendar unit. -/
#guard match DurationComponents.ofComponents? 0 0 0 1 0 0 0 with
  | some period =>
      isTemporalSetError (TemporalSet.ofPatternPeriod (.weekday .sunday) period)
        (.incompatiblePeriod (.weekday .sunday) period)
  | none => false

#guard match MonthDay.ofNat? 2 29, DurationComponents.ofComponents? 0 12 0 0 0 0 0 with
  | some monthDay, some period =>
      isTemporalSetError (TemporalSet.ofPatternPeriod (.monthDay monthDay) period)
        (.incompatiblePeriod (.monthDay monthDay) period)
  | _, _ => false

#guard match ClockTime.ofHour? 4, DurationComponents.ofComponents? 0 0 0 0 24 0 0 with
  | some time, some period =>
      isTemporalSetError (TemporalSet.ofPatternPeriod (.time time) period)
        (.incompatiblePeriod (.time time) period)
  | _, _ => false

/- Month-day and clock patterns accept positive whole-year and whole-day cadences. -/
#guard match MonthDay.ofNat? 2 29, DurationComponents.ofComponents? 2 0 0 0 0 0 0 with
  | some monthDay, some period =>
      (TemporalSet.ofPatternPeriod (.monthDay monthDay) period).isOk
  | _, _ => false

#guard match ClockTime.ofHour? 4, DurationComponents.ofComponents? 0 0 0 2 0 0 0 with
  | some time, some period => (TemporalSet.ofPatternPeriod (.time time) period).isOk
  | _, _ => false

/- Date-time rendering concatenates one full date with one local clock value. -/
#guard match CivilDate.ofYMD? 2011 9 20, ClockTime.ofHourMinute? 16 0 with
  | some date, some time =>
      (Value.dateTime date time).kind == .time &&
        (Value.dateTime date time).renderTimex == ⟨.time, "2011-09-20T16:00", none⟩
  | _, _ => false

/- Resolution values retain both the source expression and explicit reference context. -/
#guard match CivilDate.ofYMD? 2011 9 19 with
  | some date =>
      let expression := SymbolicExpr.relativeWeekday .previous .friday
      let context : ReferenceContext := { date := some date }
      Resolution.symbolic expression context .ambiguousBareWeekday ==
        .symbolic expression context .ambiguousBareWeekday
  | none => false

/- Symbolic depth checking accepts an exact limit and rejects a one-short limit. -/
#guard match ClockTime.ofHour? 4 with
  | some time =>
      let expression := SymbolicExpr.atTime (.atTime .referenceDate time) time
      expression.depth == 3 && isDepthOk (expression.checkDepth 3) 3 &&
        isDepthError (expression.checkDepth 2) (.limitExceeded 2)
  | none => false

private def nestAtTime (count : Nat) (expression : SymbolicExpr)
    (time : ClockTime) : SymbolicExpr :=
  match count with
  | 0 => expression
  | count + 1 => nestAtTime count (.atTime expression time) time

private def deepSymbolicDepthCheck : Bool :=
  match ClockTime.ofHour? 4 with
  | none => false
  | some time =>
      let expression := nestAtTime 100000 .referenceDate time
      decide (expression.depth = 100001) &&
        isDepthOk (expression.checkDepth 100001) 100001 &&
        isDepthError (expression.checkDepth 100000) (.limitExceeded 100000)

/-- Tail-recursive symbolic depth operations handle a deeply nested boundary value. -/
example : deepSymbolicDepthCheck = true := by
  native_decide

/--
Check every candidate day 0 through 32 in every month 0 through 13 and every supported year.

The acceptance oracle is independent; every accepted value must also survive a projection and
smart-constructor round trip.
-/
private def exhaustiveConstructorRoundTrip : Bool :=
  (List.range maxYear).all fun yearIndex ↦
    let year := yearIndex + 1
    (List.range 14).all fun month ↦
      (List.range 33).all fun day ↦
        let expected := oracleValidDate year month day
        match CivilDate.ofYMD? year month day with
        | some date =>
            expected && date.year = year && date.month = month && date.day = day &&
              CivilDate.ofYMD? date.year date.month date.day = some date
        | none => !expected

/-- Exhaustive supported-domain construction agrees with the independent Gregorian oracle. -/
example : exhaustiveConstructorRoundTrip = true := by
  native_decide

private def nextMonth (year month : Nat) : Nat × Nat :=
  if month = 12 then (year + 1, 1) else (year, month + 1)

private def previousMonth (year month : Nat) : Nat × Nat :=
  if month = 1 then (year - 1, 12) else (year, month - 1)

/-- Check exact forward/backward day round trips at every supported month boundary. -/
private def exhaustiveBoundaryDayRoundTrip : Bool :=
  (List.range maxYear).all fun yearIndex ↦
    let year := yearIndex + 1
    (List.range 12).all fun monthIndex ↦
      let month := monthIndex + 1
      let lastDay := oracleDaysInMonth year month
      let forwardOk :=
        if year = maxYear && month = 12 then true
        else
          match CivilDate.ofYMD? year month lastDay with
          | none => false
          | some source =>
              match source.addDays 1 with
              | .error _ => false
              | .ok shifted =>
                  let target := nextMonth year month
                  shifted.year = target.1 && shifted.month = target.2 && shifted.day = 1 &&
                    match shifted.subDays 1 with
                    | .ok restored => decide (restored = source)
                    | .error _ => false
      let backwardOk :=
        if year = 1 && month = 1 then true
        else
          match CivilDate.ofYMD? year month 1 with
          | none => false
          | some source =>
              match source.subDays 1 with
              | .error _ => false
              | .ok shifted =>
                  let target := previousMonth year month
                  shifted.year = target.1 && shifted.month = target.2 &&
                    shifted.day = oracleDaysInMonth target.1 target.2 &&
                    match shifted.addDays 1 with
                    | .ok restored => decide (restored = source)
                    | .error _ => false
      forwardOk && backwardOk

/-- Every supported month boundary round-trips through exact day arithmetic. -/
example : exhaustiveBoundaryDayRoundTrip = true := by
  native_decide

/-- Check clipped month addition independently at every supported month boundary. -/
private def exhaustiveMonthClipping : Bool :=
  (List.range maxYear).all fun yearIndex ↦
    let year := yearIndex + 1
    (List.range 12).all fun monthIndex ↦
      let month := monthIndex + 1
      if year = maxYear && month = 12 then true
      else
        let target := nextMonth year month
        let sourceDay := oracleDaysInMonth year month
        let targetDay := min sourceDay (oracleDaysInMonth target.1 target.2)
        match CivilDate.ofYMD? year month sourceDay with
        | none => false
        | some source => isDate (source.addMonthsClip 1) target.1 target.2 targetDay

/-- Clipped month addition agrees with an independent oracle at every month end. -/
example : exhaustiveMonthClipping = true := by
  native_decide

end NlpTests.Core.Temporal
