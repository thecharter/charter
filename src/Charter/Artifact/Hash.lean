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

def stringToUtf8List : List Char → List UInt8
  | [] => []
  | c :: cs => utf8CharBytes c ++ stringToUtf8List cs

end Sha256

/-- Lowercase 64-character hex SHA-256 digest of a byte list. -/
def sha256ByteList (bs : List UInt8) : String :=
  let padded := Sha256.padMessage bs
  let st := Sha256.processBlocks (padded.length / 64 + 1) {} padded
  Sha256.digestToHex st

/-- Lowercase 64-character hex SHA-256 digest of a UTF-8 string. -/
def sha256String (s : String) : String :=
  sha256ByteList (Sha256.stringToUtf8List s.toList)

/-- NIST FIPS 180-4 SHA-256 test vectors (empty, single-block, and multi-block),
verified inside the Lean kernel with zero axioms. -/
theorem sha256_nist_vectors :
    sha256String "" = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" ∧
    sha256String "abc" = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" ∧
    sha256String "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" =
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" := by
  decide +kernel

#print axioms sha256_nist_vectors

end Charter.Artifact
