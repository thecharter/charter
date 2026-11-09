/-!
# Charter.Artifact.Hash — Pure Kernel-Reducible FIPS 180-4 SHA-256

Computes standard 256-bit SHA-256 digests (`sha256Bytes`, `sha256String`) using pure
structural recursion over `UInt32` words with zero `@[extern]` FFI, zero `partial`, and
zero extra axioms (`Law 10`, `D18`). Compile-time `rfl` theorems verify single-block and
multi-block NIST FIPS 180-4 test vectors directly inside the Lean kernel.
-/

namespace Charter.Artifact

namespace Sha256

def kTable : List UInt32 := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

structure DigestState where
  h0 : UInt32 := 0x6a09e667
  h1 : UInt32 := 0xbb67ae85
  h2 : UInt32 := 0x3c6ef372
  h3 : UInt32 := 0xa54ff53a
  h4 : UInt32 := 0x510e527f
  h5 : UInt32 := 0x9b05688c
  h6 : UInt32 := 0x1f83d9ab
  h7 : UInt32 := 0x5be0cd19
  deriving Repr, DecidableEq

def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~x) &&& z)
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def wordAt : List UInt32 → Nat → UInt32
  | [], _ => 0
  | w :: _, 0 => w
  | _ :: ws, n + 1 => wordAt ws n

def bytesToWords : Nat → List UInt8 → List UInt32
  | 0, _ => []
  | k + 1, b0 :: b1 :: b2 :: b3 :: rest =>
    let w : UInt32 :=
      (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32
    w :: bytesToWords k rest
  | _, _ => []

def expandSchedule (w16 : List UInt32) : List UInt32 :=
  let rec go (idx : Nat) : Nat → List UInt32 → List UInt32
    | 0, ws => ws
    | rem + 1, ws =>
      let wNew := smallSigma1 (wordAt ws (idx - 2)) + wordAt ws (idx - 7) +
                  smallSigma0 (wordAt ws (idx - 15)) + wordAt ws (idx - 16)
      go (idx + 1) rem (ws ++ [wNew])
  go 16 48 w16

def compressRounds : List UInt32 → List UInt32 → DigestState → DigestState
  | k :: ks, w :: ws, s =>
    let t1 := s.h7 + bigSigma1 s.h4 + ch s.h4 s.h5 s.h6 + k + w
    let t2 := bigSigma0 s.h0 + maj s.h0 s.h1 s.h2
    let next : DigestState := {
      h0 := t1 + t2
      h1 := s.h0
      h2 := s.h1
      h3 := s.h2
      h4 := s.h3 + t1
      h5 := s.h4
      h6 := s.h5
      h7 := s.h6
    }
    compressRounds ks ws next
  | _, _, s => s

def compressBlock (s : DigestState) (block64 : List UInt8) : DigestState :=
  let w64 := expandSchedule (bytesToWords 16 block64)
  let r := compressRounds kTable w64 s
  { h0 := s.h0 + r.h0, h1 := s.h1 + r.h1, h2 := s.h2 + r.h2, h3 := s.h3 + r.h3,
    h4 := s.h4 + r.h4, h5 := s.h5 + r.h5, h6 := s.h6 + r.h6, h7 := s.h7 + r.h7 }

def takeDrop64 : List UInt8 → List UInt8 × List UInt8
  | bs => (bs.take 64, bs.drop 64)

def processBlocks : Nat → DigestState → List UInt8 → DigestState
  | 0, s, _ => s
  | _, s, [] => s
  | fuel + 1, s, bs =>
    let (blk, rest) := takeDrop64 bs
    processBlocks fuel (compressBlock s blk) rest

def uint64ToBeBytes (n : UInt64) : List UInt8 := [
  (n >>> 56).toUInt8, (n >>> 48).toUInt8, (n >>> 40).toUInt8, (n >>> 32).toUInt8,
  (n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8
]

def padMessage (bs : List UInt8) : List UInt8 :=
  let len := bs.length
  let zeroCount := (55 + 64 - (len % 64)) % 64
  let bitLen : UInt64 := len.toUInt64 * 8
  bs ++ [0x80] ++ List.replicate zeroCount 0x00 ++ uint64ToBeBytes bitLen

def hexNibble (n : UInt32) : Char :=
  let v := (n &&& 0xF).toNat
  if v < 10 then Char.ofNat (48 + v) else Char.ofNat (87 + v)

def wordToHex (w : UInt32) : List Char := [
  hexNibble (w >>> 28), hexNibble (w >>> 24), hexNibble (w >>> 20), hexNibble (w >>> 16),
  hexNibble (w >>> 12), hexNibble (w >>> 8), hexNibble (w >>> 4), hexNibble w
]

def digestToHex (s : DigestState) : String :=
  String.mk (wordToHex s.h0 ++ wordToHex s.h1 ++ wordToHex s.h2 ++ wordToHex s.h3 ++
             wordToHex s.h4 ++ wordToHex s.h5 ++ wordToHex s.h6 ++ wordToHex s.h7)

def wordToBytes (w : UInt32) : List UInt8 := [
  (w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8
]

def digestToBytes (s : DigestState) : List UInt8 :=
  wordToBytes s.h0 ++ wordToBytes s.h1 ++ wordToBytes s.h2 ++ wordToBytes s.h3 ++
  wordToBytes s.h4 ++ wordToBytes s.h5 ++ wordToBytes s.h6 ++ wordToBytes s.h7

def utf8CharBytes (c : Char) : List UInt8 :=
  let u := c.val
  if u ≤ 0x7F then [u.toUInt8]
  else if u ≤ 0x7FF then
    [((0xC0 : UInt32) ||| (u >>> 6)).toUInt8, ((0x80 : UInt32) ||| (u &&& 0x3F)).toUInt8]
  else if u ≤ 0xFFFF then
    [((0xE0 : UInt32) ||| (u >>> 12)).toUInt8,
     ((0x80 : UInt32) ||| ((u >>> 6) &&& 0x3F)).toUInt8,
     ((0x80 : UInt32) ||| (u &&& 0x3F)).toUInt8]
  else
    [((0xF0 : UInt32) ||| (u >>> 18)).toUInt8,
     ((0x80 : UInt32) ||| ((u >>> 12) &&& 0x3F)).toUInt8,
     ((0x80 : UInt32) ||| ((u >>> 6) &&& 0x3F)).toUInt8,
     ((0x80 : UInt32) ||| (u &&& 0x3F)).toUInt8]

def stringToUtf8Acc : List Char → List UInt8 → List UInt8
  | [], acc => acc.reverse
  | c :: cs, acc => stringToUtf8Acc cs ((utf8CharBytes c).reverse ++ acc)

def stringToUtf8List (cs : List Char) : List UInt8 :=
  stringToUtf8Acc cs []

end Sha256

/-- Lowercase 64-character hex SHA-256 digest of a byte list. -/
def sha256ByteList (bs : List UInt8) : String :=
  let padded := Sha256.padMessage bs
  let st := Sha256.processBlocks (padded.length / 64 + 1) {} padded
  Sha256.digestToHex st

/-- Raw 32-byte SHA-256 digest of a byte list. -/
def sha256RawBytes (bs : List UInt8) : List UInt8 :=
  let padded := Sha256.padMessage bs
  let st := Sha256.processBlocks (padded.length / 64 + 1) {} padded
  Sha256.digestToBytes st

/-- Lowercase 64-character hex SHA-256 digest of a UTF-8 string. -/
def sha256String (s : String) : String :=
  sha256ByteList (Sha256.stringToUtf8List s.toList)

/-- Pure-Lean RFC 2104 HMAC-SHA256 (`D27`, `G4.1`): authenticates `.artifact` certificates,
hash-chained server log entries, and short-lived capability tokens with zero C/FFI dependencies. -/
def hmacSha256Bytes (key msg : List UInt8) : String :=
  let keyNorm := if 64 < key.length then sha256RawBytes key else key
  let keyPad := keyNorm ++ List.replicate (64 - keyNorm.length) 0x00
  let ipad := keyPad.map (fun b => b ^^^ (0x36 : UInt8))
  let opad := keyPad.map (fun b => b ^^^ (0x5c : UInt8))
  let inner := sha256RawBytes (ipad ++ msg)
  sha256ByteList (opad ++ inner)

def hmacSha256 (key msg : String) : String :=
  hmacSha256Bytes (Sha256.stringToUtf8List key.toList) (Sha256.stringToUtf8List msg.toList)

/-- NIST FIPS 180-4 SHA-256 test vectors (empty, single-block, and multi-block),
verified inside the Lean kernel with zero axioms. -/
theorem sha256_nist_vectors :
    sha256String "" = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" ∧
    sha256String "abc" = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" ∧
    sha256String "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" =
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" := by
  decide +kernel

/-- RFC 4231 Test Case 2 (`key = "Jefe"`, `data = "what do ya want for nothing?"`),
verified inside the Lean kernel via `decide +kernel`. -/
theorem hmacSha256_rfc4231_vector :
    hmacSha256 "Jefe" "what do ya want for nothing?" =
      "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843" := by
  decide +kernel

/-! ## Per-Actor Schnorr Public-Key Signatures (`#76`)
Subgroup order `q = 2^255 - 19`, modulus `p = (2^257 + 22) * q + 1`, generator `g = 2^(2^257 + 22) mod p`.
Public keys `pk = g^sk mod p` bind actors in `.artifact` or `State` without revealing `sk`. -/

def schnorrP : Nat :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe4fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe5f

def schnorrQ : Nat :=
  0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed

def schnorrG : Nat :=
  0x92682eb410d1295964cd1e6fb8eeb538be540e23ac7af7281785f2d372a9ba5a0c43e5161cc1a8c29cc353133797abf5e9613199ed9a744b63b42679f65a9934

def powModLoop : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, acc => acc
  | fuel + 1, base, exp, m, acc =>
    if exp == 0 then acc
    else
      let acc' := if exp % 2 == 1 then (acc * base) % m else acc
      powModLoop fuel ((base * base) % m) (exp / 2) m acc'

def powMod (base exp m : Nat) : Nat :=
  if m <= 1 then 0 else powModLoop 520 (base % m) exp m 1

def hexDigitVal (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then some (c.toNat - '0'.toNat)
  else if 'a' <= c && c <= 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' <= c && c <= 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

def parseHexNatChars : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc =>
    match hexDigitVal c with
    | some d => parseHexNatChars cs (acc * 16 + d)
    | none => none

def parseHexNat (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty then none else parseHexNatChars cs 0

def natToHexChars : Nat → Nat → List Char → List Char
  | 0, _, acc => if acc.isEmpty then ['0'] else acc
  | fuel + 1, n, acc =>
    if n == 0 then (if acc.isEmpty then ['0'] else acc)
    else
      let nib := n % 16
      let ch := if nib < 10 then Char.ofNat ('0'.toNat + nib) else Char.ofNat ('a'.toNat + nib - 10)
      natToHexChars fuel (n / 16) (ch :: acc)

def natToHex (n : Nat) : String :=
  String.mk (natToHexChars 140 n [])

def sha256ScalarModQ (s : String) : Nat :=
  let raw := (parseHexNat (sha256String s)).getD 1
  (raw % (schnorrQ - 1)) + 1

/-- Derive an actor's hex public key `pk = g^sk mod p` from their private seed (`#76`). -/
def deriveActorPubKey (privSeed : String) : String :=
  let sk := sha256ScalarModQ ("charter-actor-sk-v1:" ++ privSeed)
  natToHex (powMod schnorrG sk schnorrP)

/-- Produce a deterministic Schnorr signature `<R_hex>:<s_hex>` over `msg` (`#76`). -/
def signActorMsg (privSeed msg : String) : String :=
  let sk := sha256ScalarModQ ("charter-actor-sk-v1:" ++ privSeed)
  let pkHex := natToHex (powMod schnorrG sk schnorrP)
  let k := sha256ScalarModQ ("charter-actor-nonce-v1:" ++ privSeed ++ ":" ++ msg)
  let rVal := powMod schnorrG k schnorrP
  let rHex := natToHex rVal
  let e := sha256ScalarModQ ("charter-actor-sig-v1:" ++ rHex ++ ":" ++ pkHex ++ ":" ++ msg)
  let sVal := (k + e * sk) % schnorrQ
  rHex ++ ":" ++ natToHex sVal

/-- Verify a Schnorr actor signature using ONLY `pubKeyHex` (never needing `privSeed`, `#76`). -/
def verifyActorSig (pubKeyHex msg sig : String) : Bool :=
  match pubKeyHex.toLower, sig.splitOn ":" with
  | pkNorm, [rStr, sStr] =>
    let rNorm := rStr.toLower
    match parseHexNat pkNorm, parseHexNat rNorm, parseHexNat sStr with
    | some pk, some rVal, some sVal =>
      if pk <= 1 || pk >= schnorrP || rVal <= 1 || rVal >= schnorrP || sVal >= schnorrQ then false
      else
        let e := sha256ScalarModQ ("charter-actor-sig-v1:" ++ rNorm ++ ":" ++ pkNorm ++ ":" ++ msg)
        let lhs := powMod schnorrG sVal schnorrP
        let rhs := (rVal * powMod pk e schnorrP) % schnorrP
        lhs == rhs && powMod pk schnorrQ schnorrP == 1
    | _, _, _ => false
  | _, _ => false

#print axioms sha256_nist_vectors

end Charter.Artifact
