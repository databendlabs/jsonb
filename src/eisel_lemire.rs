// Adapted from fast-float2 0.2.4 (`src/binary.rs` and `src/table.rs`),
// https://github.com/Alexhuszagh/fast-float-rust, by Ivan Smirnov and
// Alex Huszagh, licensed under MIT OR Apache-2.0 and used here under the
// Apache License, Version 2.0. fast-float2 is a port of fast_float by
// Daniel Lemire, https://github.com/fastfloat/fast_float.
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

//! The Eisel-Lemire algorithm: the `f64` nearest to `mantissa / 10^scale`,
//! computed from the integers without formatting them as text.
//!
//! fast-float2 keeps `compute_float` private and only parses text, so it is
//! copied here. Changes from upstream:
//! - specialized to `f64`;
//! - returns `None` where upstream returns `power2 = -1`, so the caller falls
//!   back to parsing text;
//! - the power-of-five table keeps only the exponents -255..=0 that a `u8`
//!   scale can produce, indexed by the scale so the lookup needs no bounds
//!   check.
//!
//! Upstream's `parse_float` also re-runs the algorithm with `mantissa + 1`
//! when the text had more than 19 digits; a decimal's mantissa is exact, so
//! that step does not apply.

const MANTISSA_EXPLICIT_BITS: usize = 52;
const MIN_EXPONENT_ROUND_TO_EVEN: i64 = -4;
const MAX_EXPONENT_ROUND_TO_EVEN: i64 = 23;
const MINIMUM_EXPONENT: i32 = -1023;
const INFINITE_POWER: i32 = 0x7FF;
const SIGN_INDEX: usize = 63;

/// Returns the `f64` nearest to `mantissa / 10^scale`, negated if `negative`,
/// or `None` if the 128-bit product cannot decide the rounding. On `None`,
/// parse the decimal text instead.
#[inline]
pub(crate) fn decimal_to_f64(negative: bool, mantissa: u64, scale: u8) -> Option<f64> {
    let (mantissa, power2) = compute_float(scale, mantissa)?;
    let mut word = mantissa;
    word |= (power2 as u64) << MANTISSA_EXPLICIT_BITS;
    if negative {
        word |= 1_u64 << SIGN_INDEX;
    }
    Some(f64::from_bits(word))
}

/// Upstream `compute_float::<f64>(q, w)` with `q = -scale`, returning the
/// `(mantissa, power2)` of the adjusted mantissa.
#[inline]
fn compute_float(scale: u8, mut w: u64) -> Option<(u64, i32)> {
    let q = -i64::from(scale);
    // Upstream also returns zero or infinity for `q` outside -342..=308,
    // which a `u8` scale cannot reach.
    if w == 0 {
        return Some((0, 0));
    }
    let lz = w.leading_zeros();
    w <<= lz;
    let (lo, hi) = compute_product_approx(scale, w, MANTISSA_EXPLICIT_BITS + 3);
    if lo == 0xFFFF_FFFF_FFFF_FFFF {
        let inside_safe_exponent = (-27..=55).contains(&q);
        if !inside_safe_exponent {
            return None;
        }
    }
    let upperbit = (hi >> 63) as i32;
    let mut mantissa = hi >> (upperbit + 64 - MANTISSA_EXPLICIT_BITS as i32 - 3);
    let mut power2 = power(q as i32) + upperbit - lz as i32 - MINIMUM_EXPONENT;
    if power2 <= 0 {
        if -power2 + 1 >= 64 {
            return Some((0, 0));
        }
        mantissa >>= -power2 + 1;
        mantissa += mantissa & 1;
        mantissa >>= 1;
        power2 = (mantissa >= (1_u64 << MANTISSA_EXPLICIT_BITS)) as i32;
        return Some((mantissa, power2));
    }
    if lo <= 1
        && (MIN_EXPONENT_ROUND_TO_EVEN..=MAX_EXPONENT_ROUND_TO_EVEN).contains(&q)
        && mantissa & 3 == 1
        && (mantissa << (upperbit + 64 - MANTISSA_EXPLICIT_BITS as i32 - 3)) == hi
    {
        mantissa &= !1_u64;
    }
    mantissa += mantissa & 1;
    mantissa >>= 1;
    if mantissa >= (2_u64 << MANTISSA_EXPLICIT_BITS) {
        mantissa = 1_u64 << MANTISSA_EXPLICIT_BITS;
        power2 += 1;
    }
    mantissa &= !(1_u64 << MANTISSA_EXPLICIT_BITS);
    if power2 >= INFINITE_POWER {
        return Some((0, INFINITE_POWER));
    }
    Some((mantissa, power2))
}

#[inline]
fn power(q: i32) -> i32 {
    (q.wrapping_mul(152_170 + 65536) >> 16) + 63
}

#[inline]
fn full_multiplication(a: u64, b: u64) -> (u64, u64) {
    let r = (a as u128) * (b as u128);
    (r as u64, (r >> 64) as u64)
}

// This will compute or rather approximate w * 5**q and return a pair of 64-bit
// words approximating the result, with the "high" part corresponding to the
// most significant bits and the low part corresponding to the least significant
// bits.
#[inline]
fn compute_product_approx(scale: u8, w: u64, precision: usize) -> (u64, u64) {
    debug_assert!(precision <= 64);

    let mask = if precision < 64 {
        0xFFFF_FFFF_FFFF_FFFF_u64 >> precision
    } else {
        0xFFFF_FFFF_FFFF_FFFF_u64
    };
    // Entry `i` holds 5^(i - 255), so 5^-scale is at `255 - scale`.
    let (lo5, hi5) = POWER_OF_FIVE_128[usize::from(u8::MAX - scale)];
    let (mut first_lo, mut first_hi) = full_multiplication(w, lo5);
    if first_hi & mask == mask {
        let (_, second_hi) = full_multiplication(w, hi5);
        first_lo = first_lo.wrapping_add(second_hi);
        if second_hi > first_lo {
            first_hi += 1;
        }
    }
    (first_lo, first_hi)
}

/// 128-bit approximations of 5^-255 through 5^0, copied from upstream's
/// `POWER_OF_FIVE_128` (entries 87..=342, upstream starts at 5^-342).
#[allow(clippy::unreadable_literal)]
const POWER_OF_FIVE_128: [(u64, u64); 256] = [
    (0xf03d93eebc589f88, 0x793555ab7eba27ca),
    (0x96267c7535b763b5, 0x4bc1558b2f3458de),
    (0xbbb01b9283253ca2, 0x9eb1aaedfb016f16),
    (0xea9c227723ee8bcb, 0x465e15a979c1cadc),
    (0x92a1958a7675175f, 0xbfacd89ec191ec9),
    (0xb749faed14125d36, 0xcef980ec671f667b),
    (0xe51c79a85916f484, 0x82b7e12780e7401a),
    (0x8f31cc0937ae58d2, 0xd1b2ecb8b0908810),
    (0xb2fe3f0b8599ef07, 0x861fa7e6dcb4aa15),
    (0xdfbdcece67006ac9, 0x67a791e093e1d49a),
    (0x8bd6a141006042bd, 0xe0c8bb2c5c6d24e0),
    (0xaecc49914078536d, 0x58fae9f773886e18),
    (0xda7f5bf590966848, 0xaf39a475506a899e),
    (0x888f99797a5e012d, 0x6d8406c952429603),
    (0xaab37fd7d8f58178, 0xc8e5087ba6d33b83),
    (0xd5605fcdcf32e1d6, 0xfb1e4a9a90880a64),
    (0x855c3be0a17fcd26, 0x5cf2eea09a55067f),
    (0xa6b34ad8c9dfc06f, 0xf42faa48c0ea481e),
    (0xd0601d8efc57b08b, 0xf13b94daf124da26),
    (0x823c12795db6ce57, 0x76c53d08d6b70858),
    (0xa2cb1717b52481ed, 0x54768c4b0c64ca6e),
    (0xcb7ddcdda26da268, 0xa9942f5dcf7dfd09),
    (0xfe5d54150b090b02, 0xd3f93b35435d7c4c),
    (0x9efa548d26e5a6e1, 0xc47bc5014a1a6daf),
    (0xc6b8e9b0709f109a, 0x359ab6419ca1091b),
    (0xf867241c8cc6d4c0, 0xc30163d203c94b62),
    (0x9b407691d7fc44f8, 0x79e0de63425dcf1d),
    (0xc21094364dfb5636, 0x985915fc12f542e4),
    (0xf294b943e17a2bc4, 0x3e6f5b7b17b2939d),
    (0x979cf3ca6cec5b5a, 0xa705992ceecf9c42),
    (0xbd8430bd08277231, 0x50c6ff782a838353),
    (0xece53cec4a314ebd, 0xa4f8bf5635246428),
    (0x940f4613ae5ed136, 0x871b7795e136be99),
    (0xb913179899f68584, 0x28e2557b59846e3f),
    (0xe757dd7ec07426e5, 0x331aeada2fe589cf),
    (0x9096ea6f3848984f, 0x3ff0d2c85def7621),
    (0xb4bca50b065abe63, 0xfed077a756b53a9),
    (0xe1ebce4dc7f16dfb, 0xd3e8495912c62894),
    (0x8d3360f09cf6e4bd, 0x64712dd7abbbd95c),
    (0xb080392cc4349dec, 0xbd8d794d96aacfb3),
    (0xdca04777f541c567, 0xecf0d7a0fc5583a0),
    (0x89e42caaf9491b60, 0xf41686c49db57244),
    (0xac5d37d5b79b6239, 0x311c2875c522ced5),
    (0xd77485cb25823ac7, 0x7d633293366b828b),
    (0x86a8d39ef77164bc, 0xae5dff9c02033197),
    (0xa8530886b54dbdeb, 0xd9f57f830283fdfc),
    (0xd267caa862a12d66, 0xd072df63c324fd7b),
    (0x8380dea93da4bc60, 0x4247cb9e59f71e6d),
    (0xa46116538d0deb78, 0x52d9be85f074e608),
    (0xcd795be870516656, 0x67902e276c921f8b),
    (0x806bd9714632dff6, 0xba1cd8a3db53b6),
    (0xa086cfcd97bf97f3, 0x80e8a40eccd228a4),
    (0xc8a883c0fdaf7df0, 0x6122cd128006b2cd),
    (0xfad2a4b13d1b5d6c, 0x796b805720085f81),
    (0x9cc3a6eec6311a63, 0xcbe3303674053bb0),
    (0xc3f490aa77bd60fc, 0xbedbfc4411068a9c),
    (0xf4f1b4d515acb93b, 0xee92fb5515482d44),
    (0x991711052d8bf3c5, 0x751bdd152d4d1c4a),
    (0xbf5cd54678eef0b6, 0xd262d45a78a0635d),
    (0xef340a98172aace4, 0x86fb897116c87c34),
    (0x9580869f0e7aac0e, 0xd45d35e6ae3d4da0),
    (0xbae0a846d2195712, 0x8974836059cca109),
    (0xe998d258869facd7, 0x2bd1a438703fc94b),
    (0x91ff83775423cc06, 0x7b6306a34627ddcf),
    (0xb67f6455292cbf08, 0x1a3bc84c17b1d542),
    (0xe41f3d6a7377eeca, 0x20caba5f1d9e4a93),
    (0x8e938662882af53e, 0x547eb47b7282ee9c),
    (0xb23867fb2a35b28d, 0xe99e619a4f23aa43),
    (0xdec681f9f4c31f31, 0x6405fa00e2ec94d4),
    (0x8b3c113c38f9f37e, 0xde83bc408dd3dd04),
    (0xae0b158b4738705e, 0x9624ab50b148d445),
    (0xd98ddaee19068c76, 0x3badd624dd9b0957),
    (0x87f8a8d4cfa417c9, 0xe54ca5d70a80e5d6),
    (0xa9f6d30a038d1dbc, 0x5e9fcf4ccd211f4c),
    (0xd47487cc8470652b, 0x7647c3200069671f),
    (0x84c8d4dfd2c63f3b, 0x29ecd9f40041e073),
    (0xa5fb0a17c777cf09, 0xf468107100525890),
    (0xcf79cc9db955c2cc, 0x7182148d4066eeb4),
    (0x81ac1fe293d599bf, 0xc6f14cd848405530),
    (0xa21727db38cb002f, 0xb8ada00e5a506a7c),
    (0xca9cf1d206fdc03b, 0xa6d90811f0e4851c),
    (0xfd442e4688bd304a, 0x908f4a166d1da663),
    (0x9e4a9cec15763e2e, 0x9a598e4e043287fe),
    (0xc5dd44271ad3cdba, 0x40eff1e1853f29fd),
    (0xf7549530e188c128, 0xd12bee59e68ef47c),
    (0x9a94dd3e8cf578b9, 0x82bb74f8301958ce),
    (0xc13a148e3032d6e7, 0xe36a52363c1faf01),
    (0xf18899b1bc3f8ca1, 0xdc44e6c3cb279ac1),
    (0x96f5600f15a7b7e5, 0x29ab103a5ef8c0b9),
    (0xbcb2b812db11a5de, 0x7415d448f6b6f0e7),
    (0xebdf661791d60f56, 0x111b495b3464ad21),
    (0x936b9fcebb25c995, 0xcab10dd900beec34),
    (0xb84687c269ef3bfb, 0x3d5d514f40eea742),
    (0xe65829b3046b0afa, 0xcb4a5a3112a5112),
    (0x8ff71a0fe2c2e6dc, 0x47f0e785eaba72ab),
    (0xb3f4e093db73a093, 0x59ed216765690f56),
    (0xe0f218b8d25088b8, 0x306869c13ec3532c),
    (0x8c974f7383725573, 0x1e414218c73a13fb),
    (0xafbd2350644eeacf, 0xe5d1929ef90898fa),
    (0xdbac6c247d62a583, 0xdf45f746b74abf39),
    (0x894bc396ce5da772, 0x6b8bba8c328eb783),
    (0xab9eb47c81f5114f, 0x66ea92f3f326564),
    (0xd686619ba27255a2, 0xc80a537b0efefebd),
    (0x8613fd0145877585, 0xbd06742ce95f5f36),
    (0xa798fc4196e952e7, 0x2c48113823b73704),
    (0xd17f3b51fca3a7a0, 0xf75a15862ca504c5),
    (0x82ef85133de648c4, 0x9a984d73dbe722fb),
    (0xa3ab66580d5fdaf5, 0xc13e60d0d2e0ebba),
    (0xcc963fee10b7d1b3, 0x318df905079926a8),
    (0xffbbcfe994e5c61f, 0xfdf17746497f7052),
    (0x9fd561f1fd0f9bd3, 0xfeb6ea8bedefa633),
    (0xc7caba6e7c5382c8, 0xfe64a52ee96b8fc0),
    (0xf9bd690a1b68637b, 0x3dfdce7aa3c673b0),
    (0x9c1661a651213e2d, 0x6bea10ca65c084e),
    (0xc31bfa0fe5698db8, 0x486e494fcff30a62),
    (0xf3e2f893dec3f126, 0x5a89dba3c3efccfa),
    (0x986ddb5c6b3a76b7, 0xf89629465a75e01c),
    (0xbe89523386091465, 0xf6bbb397f1135823),
    (0xee2ba6c0678b597f, 0x746aa07ded582e2c),
    (0x94db483840b717ef, 0xa8c2a44eb4571cdc),
    (0xba121a4650e4ddeb, 0x92f34d62616ce413),
    (0xe896a0d7e51e1566, 0x77b020baf9c81d17),
    (0x915e2486ef32cd60, 0xace1474dc1d122e),
    (0xb5b5ada8aaff80b8, 0xd819992132456ba),
    (0xe3231912d5bf60e6, 0x10e1fff697ed6c69),
    (0x8df5efabc5979c8f, 0xca8d3ffa1ef463c1),
    (0xb1736b96b6fd83b3, 0xbd308ff8a6b17cb2),
    (0xddd0467c64bce4a0, 0xac7cb3f6d05ddbde),
    (0x8aa22c0dbef60ee4, 0x6bcdf07a423aa96b),
    (0xad4ab7112eb3929d, 0x86c16c98d2c953c6),
    (0xd89d64d57a607744, 0xe871c7bf077ba8b7),
    (0x87625f056c7c4a8b, 0x11471cd764ad4972),
    (0xa93af6c6c79b5d2d, 0xd598e40d3dd89bcf),
    (0xd389b47879823479, 0x4aff1d108d4ec2c3),
    (0x843610cb4bf160cb, 0xcedf722a585139ba),
    (0xa54394fe1eedb8fe, 0xc2974eb4ee658828),
    (0xce947a3da6a9273e, 0x733d226229feea32),
    (0x811ccc668829b887, 0x806357d5a3f525f),
    (0xa163ff802a3426a8, 0xca07c2dcb0cf26f7),
    (0xc9bcff6034c13052, 0xfc89b393dd02f0b5),
    (0xfc2c3f3841f17c67, 0xbbac2078d443ace2),
    (0x9d9ba7832936edc0, 0xd54b944b84aa4c0d),
    (0xc5029163f384a931, 0xa9e795e65d4df11),
    (0xf64335bcf065d37d, 0x4d4617b5ff4a16d5),
    (0x99ea0196163fa42e, 0x504bced1bf8e4e45),
    (0xc06481fb9bcf8d39, 0xe45ec2862f71e1d6),
    (0xf07da27a82c37088, 0x5d767327bb4e5a4c),
    (0x964e858c91ba2655, 0x3a6a07f8d510f86f),
    (0xbbe226efb628afea, 0x890489f70a55368b),
    (0xeadab0aba3b2dbe5, 0x2b45ac74ccea842e),
    (0x92c8ae6b464fc96f, 0x3b0b8bc90012929d),
    (0xb77ada0617e3bbcb, 0x9ce6ebb40173744),
    (0xe55990879ddcaabd, 0xcc420a6a101d0515),
    (0x8f57fa54c2a9eab6, 0x9fa946824a12232d),
    (0xb32df8e9f3546564, 0x47939822dc96abf9),
    (0xdff9772470297ebd, 0x59787e2b93bc56f7),
    (0x8bfbea76c619ef36, 0x57eb4edb3c55b65a),
    (0xaefae51477a06b03, 0xede622920b6b23f1),
    (0xdab99e59958885c4, 0xe95fab368e45eced),
    (0x88b402f7fd75539b, 0x11dbcb0218ebb414),
    (0xaae103b5fcd2a881, 0xd652bdc29f26a119),
    (0xd59944a37c0752a2, 0x4be76d3346f0495f),
    (0x857fcae62d8493a5, 0x6f70a4400c562ddb),
    (0xa6dfbd9fb8e5b88e, 0xcb4ccd500f6bb952),
    (0xd097ad07a71f26b2, 0x7e2000a41346a7a7),
    (0x825ecc24c873782f, 0x8ed400668c0c28c8),
    (0xa2f67f2dfa90563b, 0x728900802f0f32fa),
    (0xcbb41ef979346bca, 0x4f2b40a03ad2ffb9),
    (0xfea126b7d78186bc, 0xe2f610c84987bfa8),
    (0x9f24b832e6b0f436, 0xdd9ca7d2df4d7c9),
    (0xc6ede63fa05d3143, 0x91503d1c79720dbb),
    (0xf8a95fcf88747d94, 0x75a44c6397ce912a),
    (0x9b69dbe1b548ce7c, 0xc986afbe3ee11aba),
    (0xc24452da229b021b, 0xfbe85badce996168),
    (0xf2d56790ab41c2a2, 0xfae27299423fb9c3),
    (0x97c560ba6b0919a5, 0xdccd879fc967d41a),
    (0xbdb6b8e905cb600f, 0x5400e987bbc1c920),
    (0xed246723473e3813, 0x290123e9aab23b68),
    (0x9436c0760c86e30b, 0xf9a0b6720aaf6521),
    (0xb94470938fa89bce, 0xf808e40e8d5b3e69),
    (0xe7958cb87392c2c2, 0xb60b1d1230b20e04),
    (0x90bd77f3483bb9b9, 0xb1c6f22b5e6f48c2),
    (0xb4ecd5f01a4aa828, 0x1e38aeb6360b1af3),
    (0xe2280b6c20dd5232, 0x25c6da63c38de1b0),
    (0x8d590723948a535f, 0x579c487e5a38ad0e),
    (0xb0af48ec79ace837, 0x2d835a9df0c6d851),
    (0xdcdb1b2798182244, 0xf8e431456cf88e65),
    (0x8a08f0f8bf0f156b, 0x1b8e9ecb641b58ff),
    (0xac8b2d36eed2dac5, 0xe272467e3d222f3f),
    (0xd7adf884aa879177, 0x5b0ed81dcc6abb0f),
    (0x86ccbb52ea94baea, 0x98e947129fc2b4e9),
    (0xa87fea27a539e9a5, 0x3f2398d747b36224),
    (0xd29fe4b18e88640e, 0x8eec7f0d19a03aad),
    (0x83a3eeeef9153e89, 0x1953cf68300424ac),
    (0xa48ceaaab75a8e2b, 0x5fa8c3423c052dd7),
    (0xcdb02555653131b6, 0x3792f412cb06794d),
    (0x808e17555f3ebf11, 0xe2bbd88bbee40bd0),
    (0xa0b19d2ab70e6ed6, 0x5b6aceaeae9d0ec4),
    (0xc8de047564d20a8b, 0xf245825a5a445275),
    (0xfb158592be068d2e, 0xeed6e2f0f0d56712),
    (0x9ced737bb6c4183d, 0x55464dd69685606b),
    (0xc428d05aa4751e4c, 0xaa97e14c3c26b886),
    (0xf53304714d9265df, 0xd53dd99f4b3066a8),
    (0x993fe2c6d07b7fab, 0xe546a8038efe4029),
    (0xbf8fdb78849a5f96, 0xde98520472bdd033),
    (0xef73d256a5c0f77c, 0x963e66858f6d4440),
    (0x95a8637627989aad, 0xdde7001379a44aa8),
    (0xbb127c53b17ec159, 0x5560c018580d5d52),
    (0xe9d71b689dde71af, 0xaab8f01e6e10b4a6),
    (0x9226712162ab070d, 0xcab3961304ca70e8),
    (0xb6b00d69bb55c8d1, 0x3d607b97c5fd0d22),
    (0xe45c10c42a2b3b05, 0x8cb89a7db77c506a),
    (0x8eb98a7a9a5b04e3, 0x77f3608e92adb242),
    (0xb267ed1940f1c61c, 0x55f038b237591ed3),
    (0xdf01e85f912e37a3, 0x6b6c46dec52f6688),
    (0x8b61313bbabce2c6, 0x2323ac4b3b3da015),
    (0xae397d8aa96c1b77, 0xabec975e0a0d081a),
    (0xd9c7dced53c72255, 0x96e7bd358c904a21),
    (0x881cea14545c7575, 0x7e50d64177da2e54),
    (0xaa242499697392d2, 0xdde50bd1d5d0b9e9),
    (0xd4ad2dbfc3d07787, 0x955e4ec64b44e864),
    (0x84ec3c97da624ab4, 0xbd5af13bef0b113e),
    (0xa6274bbdd0fadd61, 0xecb1ad8aeacdd58e),
    (0xcfb11ead453994ba, 0x67de18eda5814af2),
    (0x81ceb32c4b43fcf4, 0x80eacf948770ced7),
    (0xa2425ff75e14fc31, 0xa1258379a94d028d),
    (0xcad2f7f5359a3b3e, 0x96ee45813a04330),
    (0xfd87b5f28300ca0d, 0x8bca9d6e188853fc),
    (0x9e74d1b791e07e48, 0x775ea264cf55347e),
    (0xc612062576589dda, 0x95364afe032a819e),
    (0xf79687aed3eec551, 0x3a83ddbd83f52205),
    (0x9abe14cd44753b52, 0xc4926a9672793543),
    (0xc16d9a0095928a27, 0x75b7053c0f178294),
    (0xf1c90080baf72cb1, 0x5324c68b12dd6339),
    (0x971da05074da7bee, 0xd3f6fc16ebca5e04),
    (0xbce5086492111aea, 0x88f4bb1ca6bcf585),
    (0xec1e4a7db69561a5, 0x2b31e9e3d06c32e6),
    (0x9392ee8e921d5d07, 0x3aff322e62439fd0),
    (0xb877aa3236a4b449, 0x9befeb9fad487c3),
    (0xe69594bec44de15b, 0x4c2ebe687989a9b4),
    (0x901d7cf73ab0acd9, 0xf9d37014bf60a11),
    (0xb424dc35095cd80f, 0x538484c19ef38c95),
    (0xe12e13424bb40e13, 0x2865a5f206b06fba),
    (0x8cbccc096f5088cb, 0xf93f87b7442e45d4),
    (0xafebff0bcb24aafe, 0xf78f69a51539d749),
    (0xdbe6fecebdedd5be, 0xb573440e5a884d1c),
    (0x89705f4136b4a597, 0x31680a88f8953031),
    (0xabcc77118461cefc, 0xfdc20d2b36ba7c3e),
    (0xd6bf94d5e57a42bc, 0x3d32907604691b4d),
    (0x8637bd05af6c69b5, 0xa63f9a49c2c1b110),
    (0xa7c5ac471b478423, 0xfcf80dc33721d54),
    (0xd1b71758e219652b, 0xd3c36113404ea4a9),
    (0x83126e978d4fdf3b, 0x645a1cac083126ea),
    (0xa3d70a3d70a3d70a, 0x3d70a3d70a3d70a4),
    (0xcccccccccccccccc, 0xcccccccccccccccd),
    (0x8000000000000000, 0x0),
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gives_up_when_the_product_is_ambiguous() {
        // The integration tests check these inputs still convert correctly
        // through the text fallback; this checks they reach it.
        for (mantissa, scale) in [
            (14_999_775_663_049_351_983, 30),
            (16_185_735_156_734_648_777, 35),
            (18_309_340_392_174_713_697, 251),
        ] {
            assert_eq!(decimal_to_f64(false, mantissa, scale), None);
        }
        assert_eq!(decimal_to_f64(false, 0, 255), Some(0.0));
        assert_eq!(decimal_to_f64(true, 1, 0), Some(-1.0));
    }
}
