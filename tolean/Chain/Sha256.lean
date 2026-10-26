/-!
SHA-256 (FIPS 180-4), for the hashes in chain manifests. Lean's core library
has no SHA-256, and a manifest must name the exact bytes it describes.
`tests/chain` checks this implementation against `shasum -a 256`.
-/
namespace tolean.Chain

private def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The message, padded to a multiple of 64 bytes as the standard says. -/
private def pad (data : ByteArray) : ByteArray := Id.run do
  let bits : UInt64 := data.size.toUInt64 * 8
  let mut out := data.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0
  for i in [0:8] do
    out := out.push ((bits >>> ((7 - i).toUInt64 * 8)).toUInt8)
  return out

/-- The SHA-256 digest of `data`, as 32 bytes. -/
def sha256 (data : ByteArray) : ByteArray := Id.run do
  let msg := pad data
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                                 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for chunk in [0:msg.size / 64] do
    let base := chunk * 64
    let mut w : Array UInt32 := Array.replicate 64 0
    for i in [0:16] do
      let b (j : Nat) : UInt32 := (msg.get! (base + 4 * i + j)).toUInt32
      w := w.set! i ((b 0 <<< 24) ||| (b 1 <<< 16) ||| (b 2 <<< 8) ||| b 3)
    for i in [16:64] do
      let s0 := rotr w[i - 15]! 7 ^^^ rotr w[i - 15]! 18 ^^^ (w[i - 15]! >>> 3)
      let s1 := rotr w[i - 2]! 17 ^^^ rotr w[i - 2]! 19 ^^^ (w[i - 2]! >>> 10)
      w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    let mut f := h[5]!
    let mut g := h[6]!
    let mut hh := h[7]!
    for i in [0:64] do
      let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
      let ch := (e &&& f) ^^^ ((~~~e) &&& g)
      let t1 := hh + s1 + ch + roundConstants[i]! + w[i]!
      let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t2 := s0 + maj
      hh := g
      g := f
      f := e
      e := d + t1
      d := c
      c := b
      b := a
      a := t1 + t2
    h := #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]
  let mut out := ByteArray.empty
  for word in h do
    for shift in [24, 16, 8, 0] do
      out := out.push ((word >>> shift.toUInt32).toUInt8)
  return out

private def hexByte (b : UInt8) : String :=
  let d := "0123456789abcdef".toList
  String.ofList [d[(b / 16).toNat]!, d[(b % 16).toNat]!]

/-- The SHA-256 digest of `data`, in lower-case hex. -/
def sha256Hex (data : ByteArray) : String :=
  String.join ((sha256 data).toList.map hexByte)

end tolean.Chain
