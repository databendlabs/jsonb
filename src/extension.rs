// Copyright 2023 Datafuse Labs.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::cmp::Ordering;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;

use jiff::civil::date;
use jiff::civil::DateTime;
use jiff::fmt::strtime;
use jiff::fmt::strtime::BrokenDownTime;
use jiff::tz::Offset;
use jiff::SignedDuration;

const MICROS_PER_SEC: i64 = 1_000_000;
const MICROS_PER_MINUTE: i64 = 60 * MICROS_PER_SEC;
const MICROS_PER_HOUR: i64 = 60 * MICROS_PER_MINUTE;
const MONTHS_PER_YEAR: i32 = 12;

const TIMESTAMP_FORMAT: &str = "%Y-%m-%d %H:%M:%S%.6f";
const TIMESTAMP_TIMEZONE_FORMAT: &str = "%Y-%m-%d %H:%M:%S%.6f %z";

/// Represents extended JSON value types that are not supported in standard JSON.
///
/// Standard JSON only supports strings, numbers, booleans, null, arrays, and objects.
/// This enum provides additional data types commonly needed in database systems and
/// other applications that require more specialized data representations.
#[derive(Debug, Clone)]
pub enum ExtensionValue<'a> {
    /// Binary data (byte array), allowing efficient storage of binary content
    /// that would otherwise require base64 encoding in standard JSON
    Binary(&'a [u8]),
    /// Calendar date without time component (year, month, day)
    Date(Date),
    /// Timestamp with microsecond precision but without timezone information
    Timestamp(Timestamp),
    /// Timestamp with microsecond precision and timezone offset information
    TimestampTz(TimestampTz),
    /// Time interval representation for duration calculations
    Interval(Interval),
}

/// Represents a calendar date (year, month, day) without time component.
///
/// The value is stored as days since the Unix epoch (January 1, 1970).
/// This allows for efficient date arithmetic and comparison operations.
/// Standard JSON has no native date type and typically uses ISO 8601 strings.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct Date {
    /// Days since Unix epoch (January 1, 1970)
    /// Positive values represent dates after the epoch, negative values represent dates before
    pub value: i32,
}

/// Represents a timestamp (date and time) without timezone information.
///
/// The value is stored as microseconds since the Unix epoch (January 1, 1970 00:00:00 UTC).
/// This provides microsecond precision for timestamp operations.
/// Standard JSON has no native timestamp type and typically uses ISO 8601 strings.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct Timestamp {
    /// Microseconds since Unix epoch (January 1, 1970 00:00:00 UTC)
    pub value: i64,
}

/// Represents a timestamp with timezone information.
///
/// Combines a timestamp value with a timezone offset, allowing for
/// timezone-aware datetime operations. The timestamp is stored in UTC,
/// and the offset indicates the local timezone.
/// Standard JSON has no native timezone-aware timestamp type.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct TimestampTz {
    /// Timezone offset in seconds from UTC
    pub offset: i32,
    /// Microseconds since Unix epoch (January 1, 1970 00:00:00 UTC)
    pub value: i64,
}

/// Represents a time interval or duration.
///
/// This structure can represent complex time intervals with separate
/// components for months, days, and microseconds, allowing for precise
/// duration calculations that account for calendar irregularities.
/// Standard JSON has no native interval/duration type.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct Interval {
    /// Number of months in the interval
    pub months: i32,
    /// Number of days in the interval
    pub days: i32,
    /// Number of microseconds in the interval
    pub micros: i64,
}

impl Display for Date {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        let dur = SignedDuration::from_hours(self.value as i64 * 24);
        // Clamp out-of-range values to jiff's supported dates, like `Timestamp` does.
        let date = date(1970, 1, 1)
            .checked_add(dur)
            .unwrap_or(if self.value < 0 {
                jiff::civil::Date::MIN
            } else {
                jiff::civil::Date::MAX
            });
        write!(f, "{}", date)
    }
}

/// Converts microseconds since the Unix epoch, shifted by `offset_secs`, into a
/// civil datetime.
///
/// `jiff::Timestamp` cannot be used here: its range ends at
/// `9999-12-30T22:00:00Z` so that it stays valid in every offset, which is
/// earlier than the last representable timestamp `9999-12-31 23:59:59.999999`.
/// A civil datetime covers years -9999 to 9999. Values outside that range
/// saturate to `DateTime::MIN` or `DateTime::MAX`, so formatting never panics.
fn epoch_micros_to_datetime(micros: i64, offset_secs: i32) -> DateTime {
    let saturated = if micros < 0 {
        DateTime::MIN
    } else {
        DateTime::MAX
    };
    let Some(local_micros) = i64::from(offset_secs)
        .checked_mul(MICROS_PER_SEC)
        .and_then(|offset_micros| micros.checked_add(offset_micros))
    else {
        return saturated;
    };
    let epoch = DateTime::constant(1970, 1, 1, 0, 0, 0, 0);
    match epoch.checked_add(SignedDuration::from_micros(local_micros)) {
        Ok(datetime) => datetime,
        Err(_) if local_micros < 0 => DateTime::MIN,
        Err(_) => DateTime::MAX,
    }
}

impl Display for Timestamp {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        let datetime = epoch_micros_to_datetime(self.value, 0);
        // `epoch_micros_to_datetime` saturates to a datetime within jiff's
        // range, and the format only uses fields every civil datetime has.
        let text = strtime::format(TIMESTAMP_FORMAT, datetime)
            .expect("a civil datetime always formats with TIMESTAMP_FORMAT");
        f.write_str(&text)
    }
}

impl Display for TimestampTz {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        // Clamp out-of-range offsets to jiff's supported range, like the timestamp.
        let offset = self
            .offset
            .clamp(Offset::MIN.seconds(), Offset::MAX.seconds());
        let tz_offset =
            Offset::from_seconds(offset).expect("the offset is clamped to jiff's range");
        let local = epoch_micros_to_datetime(self.value, tz_offset.seconds());
        let mut tm = BrokenDownTime::from(local);
        tm.set_offset(Some(tz_offset));

        // The datetime is saturated to jiff's range and the offset clamped to a
        // valid one, so every field the format uses, including `%z`, is set.
        let text = tm.to_string(TIMESTAMP_TIMEZONE_FORMAT).expect(
            "a civil datetime with an offset always formats with TIMESTAMP_TIMEZONE_FORMAT",
        );
        f.write_str(&text)
    }
}

impl Display for Interval {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        let mut wrote_date_part = false;
        let years = self.months / MONTHS_PER_YEAR;
        let months = self.months % MONTHS_PER_YEAR;

        let mut write_component = |value: i32, singular: &str, plural: &str| -> std::fmt::Result {
            if value != 0 {
                if wrote_date_part {
                    write!(f, " ")?;
                }
                let abs_val = value.unsigned_abs();
                let unit = if abs_val == 1 { singular } else { plural };
                if value < 0 {
                    write!(f, "-{} {}", abs_val, unit)?;
                } else {
                    write!(f, "{} {}", abs_val, unit)?;
                }
                wrote_date_part = true;
            }
            Ok(())
        };

        write_component(years, "year", "years")?;
        write_component(months, "month", "months")?;
        write_component(self.days, "day", "days")?;

        if self.micros != 0 {
            if wrote_date_part {
                write!(f, " ")?;
            }
            if self.micros < 0 {
                write!(f, "-")?;
            }
            // `unsigned_abs` avoids overflow for `i64::MIN`.
            let mut micros = self.micros.unsigned_abs();
            let hour = micros / MICROS_PER_HOUR as u64;
            micros -= hour * MICROS_PER_HOUR as u64;
            let min = micros / MICROS_PER_MINUTE as u64;
            micros -= min * MICROS_PER_MINUTE as u64;
            let sec = micros / MICROS_PER_SEC as u64;
            micros -= sec * MICROS_PER_SEC as u64;

            if hour < 100 {
                write!(f, "{:02}:{:02}:{:02}", hour, min, sec)?;
            } else {
                write!(f, "{}:{:02}:{:02}", hour, min, sec)?;
            }
            if micros != 0 {
                write!(f, ".{:06}", micros)?;
            }
        } else if !wrote_date_part {
            write!(f, "00:00:00")?;
        }
        Ok(())
    }
}

impl Display for ExtensionValue<'_> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            ExtensionValue::Binary(v) => {
                for c in *v {
                    write!(f, "{c:02X}")?;
                }
                Ok(())
            }
            ExtensionValue::Date(v) => write!(f, "{}", v),
            ExtensionValue::Timestamp(v) => write!(f, "{}", v),
            ExtensionValue::TimestampTz(v) => write!(f, "{}", v),
            ExtensionValue::Interval(v) => write!(f, "{}", v),
        }
    }
}

impl Eq for ExtensionValue<'_> {}

impl PartialEq for ExtensionValue<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

#[allow(clippy::non_canonical_partial_ord_impl)]
impl PartialOrd for ExtensionValue<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let self_level = match self {
            ExtensionValue::Binary(_) => 0,
            ExtensionValue::Date(_) => 1,
            ExtensionValue::Timestamp(_) => 2,
            ExtensionValue::TimestampTz(_) => 3,
            ExtensionValue::Interval(_) => 4,
        };
        let other_level = match other {
            ExtensionValue::Binary(_) => 0,
            ExtensionValue::Date(_) => 1,
            ExtensionValue::Timestamp(_) => 2,
            ExtensionValue::TimestampTz(_) => 3,
            ExtensionValue::Interval(_) => 4,
        };
        let res = self_level.cmp(&other_level);
        if matches!(res, Ordering::Greater | Ordering::Less) {
            return Some(res);
        }

        match (self, other) {
            (ExtensionValue::Binary(self_data), ExtensionValue::Binary(other_data)) => {
                Some(self_data.cmp(other_data))
            }
            (ExtensionValue::Date(self_data), ExtensionValue::Date(other_data)) => {
                Some(self_data.cmp(other_data))
            }
            (ExtensionValue::Timestamp(self_data), ExtensionValue::Timestamp(other_data)) => {
                Some(self_data.cmp(other_data))
            }
            (ExtensionValue::TimestampTz(self_data), ExtensionValue::TimestampTz(other_data)) => {
                Some(self_data.cmp(other_data))
            }
            (ExtensionValue::Interval(self_data), ExtensionValue::Interval(other_data)) => {
                Some(self_data.cmp(other_data))
            }
            (_, _) => None,
        }
    }
}
