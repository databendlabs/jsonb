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
use jiff::fmt::strtime;
use jiff::tz::Offset;
use jiff::SignedDuration;

const MICROS_PER_SEC: i64 = 1_000_000;
const MICROS_PER_MINUTE: i64 = 60 * MICROS_PER_SEC;
const MICROS_PER_HOUR: i64 = 60 * MICROS_PER_MINUTE;
const MONTHS_PER_YEAR: i32 = 12;

const TIMESTAMP_FORMAT: &str = "%Y-%m-%d %H:%M:%S%.6f";

#[derive(Debug, Clone)]
pub enum ExtensionValue<'a> {
    Binary(&'a [u8]),
    Date(Date),
    Timestamp(Timestamp),
    TimestampTz(TimestampTz),
    Interval(Interval),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Date {
    pub value: i32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Timestamp {
    pub value: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimestampTz {
    pub offset: i8,
    pub value: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Interval {
    pub months: i32,
    pub days: i32,
    pub micros: i64,
}

impl Display for Date {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        let dur = SignedDuration::from_hours(self.value as i64 * 24);
        let date = date(1970, 1, 1).checked_add(dur).unwrap();
        write!(f, "{}", date)
    }
}

impl Display for Timestamp {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        let micros = self.value;
        let (mut secs, mut nanos) = (micros / MICROS_PER_SEC, (micros % MICROS_PER_SEC) * 1_000);
        if nanos < 0 {
            secs -= 1;
            nanos += 1_000_000_000;
        }

        if secs > 253402207200 {
            secs = 253402207200;
            nanos = 0;
        } else if secs < -377705023201 {
            secs = -377705023201;
            nanos = 0;
        }
        let ts = jiff::Timestamp::new(secs, nanos as i32).unwrap();

        write!(f, "{}", strtime::format(TIMESTAMP_FORMAT, ts).unwrap())
    }
}

impl Display for TimestampTz {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        let micros = self.value;
        let (mut secs, mut nanos) = (micros / MICROS_PER_SEC, (micros % MICROS_PER_SEC) * 1_000);
        if nanos < 0 {
            secs -= 1;
            nanos += 1_000_000_000;
        }

        if secs > 253402207200 {
            secs = 253402207200;
            nanos = 0;
        } else if secs < -377705023201 {
            secs = -377705023201;
            nanos = 0;
        }
        let ts = jiff::Timestamp::new(secs, nanos as i32).unwrap();
        let tz = Offset::constant(self.offset).to_time_zone();
        let zoned = ts.to_zoned(tz);

        write!(f, "{}", strtime::format(TIMESTAMP_FORMAT, &zoned).unwrap())
    }
}

impl Display for Interval {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        let mut date_parts = vec![];
        let years = self.months / MONTHS_PER_YEAR;
        let months = self.months % MONTHS_PER_YEAR;
        match years.cmp(&1) {
            Ordering::Equal => {
                date_parts.push((years, "year"));
            }
            Ordering::Greater => {
                date_parts.push((years, "years"));
            }
            _ => {}
        }
        match months.cmp(&1) {
            Ordering::Equal => {
                date_parts.push((months, "month"));
            }
            Ordering::Greater => {
                date_parts.push((months, "months"));
            }
            _ => {}
        }
        match self.days.cmp(&1) {
            Ordering::Equal => {
                date_parts.push((self.days, "day"));
            }
            Ordering::Greater => {
                date_parts.push((self.days, "days"));
            }
            _ => {}
        }
        if !date_parts.is_empty() {
            for (i, (val, name)) in date_parts.into_iter().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                write!(f, "{} {}", val, name)?;
            }
            if self.micros != 0 {
                write!(f, " ")?;
            }
        }

        if self.micros != 0 {
            let mut micros = self.micros;
            if micros < 0 {
                write!(f, "-")?;
                micros = -micros;
            }
            let hour = micros / MICROS_PER_HOUR;
            micros -= hour * MICROS_PER_HOUR;
            let min = micros / MICROS_PER_MINUTE;
            micros -= min * MICROS_PER_MINUTE;
            let sec = micros / MICROS_PER_SEC;
            micros -= sec * MICROS_PER_SEC;

            if hour < 100 {
                write!(f, "{:02}:{:02}:{:02}", hour, min, sec)?;
            } else {
                write!(f, "{}:{:02}:{:02}", hour, min, sec)?;
            }
            if micros != 0 {
                write!(f, ".{:06}", micros)?;
            }
        } else if self.months == 0 && self.days == 0 {
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
            ExtensionValue::Binary(_) => 4,
            ExtensionValue::Date(_) => 3,
            ExtensionValue::Timestamp(_) => 2,
            ExtensionValue::TimestampTz(_) => 1,
            ExtensionValue::Interval(_) => 0,
        };
        let other_level = match other {
            ExtensionValue::Binary(_) => 4,
            ExtensionValue::Date(_) => 3,
            ExtensionValue::Timestamp(_) => 2,
            ExtensionValue::TimestampTz(_) => 1,
            ExtensionValue::Interval(_) => 0,
        };
        if self_level > other_level {
            return Some(Ordering::Greater);
        } else if self_level < other_level {
            return Some(Ordering::Less);
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
        }
    }
}
