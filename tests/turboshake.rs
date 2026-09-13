//! TurboSHAKE128 / TurboSHAKE256 against RFC 9861 §5, transcribed unchanged
//! into `tests/vectors/RFC9861-TurboSHAKE.txt` (the test-vector section up
//! to the KangarooTwelve vectors), and against the RustCrypto `sha3` crate
//! with inputs split at random points around every rate boundary, for every
//! domain byte the RFC exercises.

use sha3::digest::{ExtendableOutput, Update, XofReader};
use solana_shake::{Shake, TurboShake128, TurboShake256};

fn run<const BITS: usize, const D: u8>(input: &[u8], out_len: usize) -> Vec<u8> {
    let mut s = Shake::<BITS, true>::new();
    s.absorb(input);
    let mut x = s.finalize::<D>();
    let mut out = vec![0u8; out_len];
    let (chunks, tail) = out.as_chunks_mut::<32>();
    for chunk in chunks {
        x.squeeze(chunk);
    }
    for byte in tail {
        let mut one = [0u8; 1];
        x.squeeze(&mut one);
        *byte = one[0];
    }
    out
}

/// The domain byte is a const parameter; the vectors and the differential
/// cover every value RFC 9861 §5 uses.
const DOMAINS: [u8; 7] = [0x01, 0x06, 0x07, 0x0B, 0x1F, 0x30, 0x7F];

macro_rules! dispatch {
    ($bits:literal, $d:expr, $input:expr, $len:expr) => {
        match $d {
            0x01 => run::<$bits, 0x01>($input, $len),
            0x06 => run::<$bits, 0x06>($input, $len),
            0x07 => run::<$bits, 0x07>($input, $len),
            0x0B => run::<$bits, 0x0B>($input, $len),
            0x1F => run::<$bits, 0x1F>($input, $len),
            0x30 => run::<$bits, 0x30>($input, $len),
            0x7F => run::<$bits, 0x7F>($input, $len),
            other => panic!("no dispatch for domain {other:#04x}"),
        }
    };
}

fn turbo(bits: usize, d: u8, input: &[u8], len: usize) -> Vec<u8> {
    match bits {
        128 => dispatch!(128, d, input, len),
        256 => dispatch!(256, d, input, len),
        _ => unreachable!(),
    }
}

/// `ptn(n)`: the pattern `00 01 .. FA` repeated and truncated to `n` bytes.
fn ptn(n: usize) -> Vec<u8> {
    (0..n).map(|i| (i % 0xFB) as u8).collect()
}

fn unhex(text: &str) -> Vec<u8> {
    text.split_whitespace()
        .map(|b| u8::from_str_radix(b, 16).unwrap())
        .collect()
}

struct Vector {
    bits: usize,
    domain: u8,
    message: Vec<u8>,
    len: usize,
    last32: bool,
    output: Vec<u8>,
}

/// `TurboSHAKE{128,256}(M=…, D=`xx`, n)[, last 32 bytes]:`.
fn header(line: &str) -> Option<(usize, &str, u8, usize, bool)> {
    let rest = line.trim().strip_prefix("TurboSHAKE")?;
    let bits: usize = rest.get(..3)?.parse().ok()?;
    let rest = rest.get(3..)?.strip_prefix("(M=")?;
    let (m, rest) = rest.split_once(", D=`")?;
    let (d, rest) = rest.split_once("`, ")?;
    let (len, rest) = rest.split_once(')')?;
    let last32 = match rest {
        ":" => false,
        ", last 32 bytes:" => true,
        _ => return None,
    };
    Some((
        bits,
        m,
        u8::from_str_radix(d, 16).ok()?,
        len.parse().ok()?,
        last32,
    ))
}

fn is_hex_line(line: &str) -> bool {
    let line = line.replace('`', "");
    !line.trim().is_empty()
        && line
            .split_whitespace()
            .all(|b| b.len() == 2 && u8::from_str_radix(b, 16).is_ok())
}

/// Each header and the hex lines that follow it, skipping the RFC's page
/// breaks; the pattern examples before the first header are not collected.
fn vectors() -> Vec<Vector> {
    let lines: Vec<&str> = include_str!("vectors/RFC9861-TurboSHAKE.txt")
        .lines()
        .collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let Some((bits, m, domain, len, last32)) = header(lines[i]) else {
            i += 1;
            continue;
        };
        let message = match m {
            "`00`^0" => Vec::new(),
            m if m.starts_with("ptn(17**") => {
                let k: u32 = m["ptn(17**".len()..]
                    .split(' ')
                    .next()
                    .unwrap()
                    .parse()
                    .unwrap();
                ptn(17usize.pow(k))
            }
            m => unhex(m.trim_matches('`')),
        };
        let want = if last32 { 32 } else { len };
        let mut output = Vec::with_capacity(want);
        i += 1;
        while output.len() < want {
            let line = lines[i];
            assert!(header(line).is_none(), "short output before {line}");
            if is_hex_line(line) {
                output.extend(unhex(&line.replace('`', "")));
            }
            i += 1;
        }
        assert_eq!(output.len(), want);
        out.push(Vector {
            bits,
            domain,
            message,
            len,
            last32,
            output,
        });
    }
    out
}

#[test]
fn rfc9861_vectors() {
    let all = vectors();
    assert_eq!(
        all.len(),
        31,
        "RFC 9861 §5 lists 16 TurboSHAKE128 and 15 TurboSHAKE256 vectors"
    );
    for v in &all {
        let got = turbo(v.bits, v.domain, &v.message, v.len);
        let got = if v.last32 {
            &got[v.len - 32..]
        } else {
            &got[..]
        };
        assert_eq!(
            got, v.output,
            "TurboSHAKE{} D={:#04x} len={}",
            v.bits, v.domain, v.len
        );
    }
}

/// Deterministic xorshift so the differential inputs are reproducible.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn fill(&mut self, buf: &mut [u8]) {
        for b in buf {
            *b = self.next() as u8;
        }
    }
}

fn sha3_turbo(bits: usize, d: u8, input: &[u8], out_len: usize) -> Vec<u8> {
    let mut out = vec![0u8; out_len];
    if bits == 128 {
        let mut h = sha3::TurboShake128::from_core(sha3::TurboShake128Core::new(d));
        h.update(input);
        h.finalize_xof().read(&mut out);
    } else {
        let mut h = sha3::TurboShake256::from_core(sha3::TurboShake256Core::new(d));
        h.update(input);
        h.finalize_xof().read(&mut out);
    }
    out
}

/// Random input lengths around every rate boundary, absorbed in random
/// chunks, against the `sha3` crate, for both levels and every RFC domain.
#[test]
fn chunked_matches_sha3_for_every_domain() {
    let mut rng = Rng(0x5851_f42d_4c95_7f2d);
    for bits in [128usize, 256] {
        let rate = 200 - bits / 4;
        for d in DOMAINS {
            for iter in 0..400 {
                let in_len = match iter % 3 {
                    0 => rng.below(3 * rate + 8),
                    1 => rate * (1 + rng.below(3)) + rng.below(3) - 1,
                    _ => rng.below(9),
                };
                let out_len = 1 + rng.below(2 * rate + 8);
                let mut input = vec![0u8; in_len];
                rng.fill(&mut input);
                // Chunked absorb through the same const-domain dispatch: split
                // the input, absorb in pieces, then compare.
                let expected = sha3_turbo(bits, d, &input, out_len);
                let ours = chunked(bits, d, &input, out_len, &mut rng);
                assert_eq!(
                    ours, expected,
                    "TurboSHAKE{bits} D={d:#04x} in_len={in_len} out_len={out_len}"
                );
            }
        }
    }
}

fn chunked_run<const BITS: usize, const D: u8>(
    input: &[u8],
    out_len: usize,
    rng: &mut Rng,
) -> Vec<u8> {
    let mut s = Shake::<BITS, true>::new();
    let mut pos = 0;
    while pos < input.len() {
        let take = 1 + rng.below(input.len() - pos);
        s.absorb(&input[pos..pos + take]);
        pos += take;
    }
    let mut x = s.finalize::<D>();
    let mut out = Vec::with_capacity(out_len);
    while out.len() < out_len {
        let remaining = out_len - out.len();
        if remaining >= 64 && rng.below(2) == 0 {
            let mut b = [0u8; 64];
            x.squeeze(&mut b);
            out.extend_from_slice(&b);
        } else {
            let mut b = [0u8; 1];
            x.squeeze(&mut b);
            out.extend_from_slice(&b);
        }
    }
    out
}

fn chunked(bits: usize, d: u8, input: &[u8], len: usize, rng: &mut Rng) -> Vec<u8> {
    macro_rules! dispatch_chunked {
        ($bits:literal) => {
            match d {
                0x01 => chunked_run::<$bits, 0x01>(input, len, rng),
                0x06 => chunked_run::<$bits, 0x06>(input, len, rng),
                0x07 => chunked_run::<$bits, 0x07>(input, len, rng),
                0x0B => chunked_run::<$bits, 0x0B>(input, len, rng),
                0x1F => chunked_run::<$bits, 0x1F>(input, len, rng),
                0x30 => chunked_run::<$bits, 0x30>(input, len, rng),
                0x7F => chunked_run::<$bits, 0x7F>(input, len, rng),
                other => panic!("no dispatch for domain {other:#04x}"),
            }
        };
    }
    match bits {
        128 => dispatch_chunked!(128),
        256 => dispatch_chunked!(256),
        _ => unreachable!(),
    }
}

/// The rate-draining path yields the same bytes as `squeeze`, block after
/// block, on the twelve-round permutation too.
#[test]
fn rate_lanes_match_squeeze() {
    fn check<const BITS: usize, const RATE: usize>() {
        assert_eq!(RATE, Shake::<BITS, true>::RATE);
        let mut a = Shake::<BITS, true>::new();
        a.absorb(b"rate-drain");
        let mut a = a.finalize::<0x07>();
        let mut b = Shake::<BITS, true>::new();
        b.absorb(b"rate-drain");
        let mut b = b.finalize::<0x07>();
        for _ in 0..3 {
            let mut drained = Vec::with_capacity(RATE);
            for lane in a.rate_lanes() {
                drained.extend_from_slice(&lane.to_le_bytes());
            }
            a.permute();
            let mut squeezed = [0u8; RATE];
            b.squeeze(&mut squeezed);
            assert_eq!(&squeezed[..], &drained[..]);
        }
    }
    check::<128, 168>();
    check::<256, 136>();
}

/// The twelve-round sponge evaluates in a const context; the result matches
/// runtime and the RFC.
const CONST_DIGEST: [u8; 32] = {
    let mut s = TurboShake128::new();
    let mut x = s.finalize::<0x1F>();
    let mut out = [0u8; 32];
    x.squeeze(&mut out);
    out
};

#[test]
fn const_evaluation_matches_runtime_and_rfc() {
    assert_eq!(CONST_DIGEST.to_vec(), turbo(128, 0x1F, &[], 32));
    // RFC 9861 §5, TurboSHAKE128(M=`00`^0, D=`1F`, 32), first four bytes.
    assert_eq!(&CONST_DIGEST[..4], &[0x1E, 0x41, 0x5F, 0x1C]);
    let mut s = TurboShake256::new();
    s.absorb(b"lanes");
    let mut x = s.finalize::<0x0B>();
    x.permute();
    let runtime = x.rate_lanes()[3];
    const LANE: u64 = {
        let mut s = TurboShake256::new();
        s.absorb(b"lanes");
        let mut x = s.finalize::<0x0B>();
        x.permute();
        x.rate_lanes()[3]
    };
    assert_eq!(LANE, runtime);
}

#[test]
fn hashv_matches_sha3_at_rate_boundaries() {
    fn check<const BITS: usize, const D: u8>() {
        let input = [0x5a; 337];
        for len in [0, 1, 135, 136, 137, 167, 168, 169, 337] {
            let input = &input[..len];
            let expected = sha3_turbo(BITS, D, input, 400);
            assert_eq!(
                Shake::<BITS, true>::hash::<400, D>(input).as_slice(),
                expected
            );
            for split in [0, len / 2, len] {
                assert_eq!(
                    Shake::<BITS, true>::hashv::<400, D>(&[
                        &[],
                        &input[..split],
                        &[],
                        &input[split..]
                    ])
                    .as_slice(),
                    expected
                );
            }
        }
    }
    check::<128, 0x01>();
    check::<128, 0x7f>();
    check::<256, 0x01>();
    check::<256, 0x7f>();
    const EMPTY: [u8; 32] = Shake::<128, true>::hashv::<32, 0x1f>(&[]);
    assert_eq!(EMPTY, CONST_DIGEST);
}
