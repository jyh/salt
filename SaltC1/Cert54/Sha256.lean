/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Init

/-!
# C1 — SHA-256, for the certificate's data pins

`SaltC1.Cert54.Sha256.hex` is SHA-256 (FIPS 180-4) over a `ByteArray`, printed as the 64 lowercase
hex digits `shasum -a 256` prints. It exists so `SaltC1.Cert54.Data` can refuse, at elaboration, a
data file whose bytes are not the ones its pins name (`cert54Pins`): Lake does not track a file read
by `IO.FS.readFile`, so without a pin a changed table could be replayed from a stale build. Nothing
here is proved about the function; it is a check, run once per file, and it reads the file the
tables are then built from. Measured over the six data files (1.63 MB) in the interpreter: 4.2 s.
Known answers (`""` and `"abc"`) and the six files agree with `shasum -a 256` (the FX3 record).

Imports `Init` only: the certificates' import rule (`scripts/check_cert_imports.py`) holds.
Nothing here bears on twin primes.
-/

namespace SaltC1.Cert54.Sha256

/-- The 64 round constants. -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value. -/
def H0 : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Rotate right by `n` bits. -/
@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The message padded to a multiple of 64 bytes: `0x80`, zeros, the bit length big-endian. -/
def pad (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let bitLen : UInt64 := len.toUInt64 * 8
  let zeros := (120 - (len + 1) % 64) % 64
  let mut out := msg.push 0x80
  for _ in [0:zeros] do
    out := out.push 0
  for i in [0:8] do
    out := out.push (bitLen >>> (8 * (7 - i)).toUInt64).toUInt8
  return out

/-- One compression round over the 64-byte block of `p` at byte offset `off`. -/
def compress (h : Array UInt32) (p : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    let b0 := (p[off + 4 * i]!).toUInt32
    let b1 := (p[off + 4 * i + 1]!).toUInt32
    let b2 := (p[off + 4 * i + 2]!).toUInt32
    let b3 := (p[off + 4 * i + 3]!).toUInt32
    w := w.push ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3)
  for i in [16:64] do
    let w15 := w[i - 15]!
    let w2 := w[i - 2]!
    let s0 := rotr w15 7 ^^^ rotr w15 18 ^^^ (w15 >>> 3)
    let s1 := rotr w2 17 ^^^ rotr w2 19 ^^^ (w2 >>> 10)
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for i in [0:64] do
    let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := hh + S1 + ch + K[i]! + w[i]!
    let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- A hex digit, lowercase. -/
def hexDigit (n : UInt32) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- A 32-bit word as eight hex digits. -/
def hex32 (x : UInt32) : String :=
  String.ofList ((List.range 8).map fun i => hexDigit ((x >>> (28 - 4 * i).toUInt32) &&& 0xf))

/-- SHA-256 of `msg`, as `shasum -a 256` prints it. -/
def hex (msg : ByteArray) : String := Id.run do
  let p := pad msg
  let mut h := H0
  for blk in [0:p.size / 64] do
    h := compress h p (blk * 64)
  return String.join (h.toList.map hex32)

end SaltC1.Cert54.Sha256
