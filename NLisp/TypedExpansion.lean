namespace NLisp.TypedExpansion

/-! An independent typing certificate language for all runtime NLisp types.
Float literals retain binary64 bits. This module establishes typing only;
it does not give floating point or string operations an evaluation semantics.
The separate NLisp.Core calculus supplies operational theorems for its subset.
-/

inductive Ty where
  | boolean | integer | unit | floating | string | character
  | fn (argument result : Ty)
  | list (element : Ty)
  | option (element : Ty)
  deriving DecidableEq, Repr

inductive Primitive where
  | add | sub | mul | quotient | remainder
  | lt | le | gt | ge | intEq
  | fadd | fsub | fmul | fdiv | flt | fle | fgt | fge | floatEq
  | boolEq | not | stringEq | charEq | append | toFloat | truncate
  deriving DecidableEq, Repr

def binary (input output : Ty) : Ty := .fn input (.fn input output)

def Primitive.type : Primitive → Ty
  | .add | .sub | .mul => binary .integer .integer
  | .quotient | .remainder => binary .integer (.option .integer)
  | .lt | .le | .gt | .ge | .intEq => binary .integer .boolean
  | .fadd | .fsub | .fmul | .fdiv => binary .floating .floating
  | .flt | .fle | .fgt | .fge | .floatEq => binary .floating .boolean
  | .boolEq => binary .boolean .boolean
  | .not => .fn .boolean .boolean
  | .stringEq => binary .string .boolean
  | .charEq => binary .character .boolean
  | .append => binary .string .string
  | .toFloat => .fn .integer .floating
  | .truncate => .fn .floating (.option .integer)

/-- Signed integer division used by the `quotient` builtin. The magnitude
division is Nat division and the sign is applied afterward, so negative
operands truncate toward zero as GMP's `mpz_tdiv_q` does. This function is
only observed through `integerOptional` when the divisor is nonzero. -/
def truncQuotient (left right : Int) : Int :=
  let magnitude := Int.ofNat (left.natAbs / right.natAbs)
  if (left < 0) = (right < 0) then magnitude else -magnitude

/-- Extract the exponent field of an IEEE-754 binary64 encoding. -/
def binary64Exponent (bits : UInt64) : Nat := bits.toNat / 2^52 % 2^11

/-- Extract the fraction field of an IEEE-754 binary64 encoding. -/
def binary64Fraction (bits : UInt64) : Nat := bits.toNat % 2^52

/-- Exact toward-zero integer conversion specified directly over binary64
bits. Exponent `0x7ff` covers infinities and every NaN payload, which return
`none` as in NLisp's C builtin. Finite subnormals and magnitudes below one
truncate to zero. The significand/exponent arithmetic retains arbitrarily large
finite results, unlike a machine-integer conversion. -/
def binary64Truncate (bits : UInt64) : Option Int :=
  let exponent := binary64Exponent bits
  if exponent = 2^11 - 1 then none else
  let fraction := binary64Fraction bits
  let significand := if exponent = 0 then fraction else 2^52 + fraction
  let magnitude :=
    if exponent = 0 || exponent < 1023 then 0
    else if exponent ≥ 1075 then significand * 2^(exponent - 1075)
    else significand / 2^(1075 - exponent)
  let negative := bits.toNat / 2^63 = 1
  some (if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude)

/-- Every non-finite binary64 encoding is rejected by the truncation model. -/
theorem binary64Truncate_nonfinite (bits : UInt64)
    (nonfinite : binary64Exponent bits = 2^11 - 1) :
    binary64Truncate bits = none := by
  simp [binary64Truncate, nonfinite]

/-- On every finite encoding, truncation respects the binary64 sign bit. A
negative encoding may produce zero (including either signed zero and every
subnormal), while a positive encoding never produces a negative integer. -/
theorem binary64Truncate_respects_sign (bits : UInt64) (integer : Int)
    (finite : binary64Exponent bits ≠ 2^11 - 1)
    (truncated : binary64Truncate bits = some integer) :
    (bits.toNat / 2^63 = 1 → integer ≤ 0) ∧
      (bits.toNat / 2^63 ≠ 1 → 0 ≤ integer) := by
  unfold binary64Truncate at truncated
  rw [if_neg finite] at truncated
  dsimp at truncated
  split at truncated
  · have signEq := truncated
    have signValueEq := Option.some.inj signEq
    have signProof : integer ≤ 0 := by
      rw [← signValueEq]
      omega
    exact ⟨fun _ => signProof, fun different => by simp_all⟩
  · have magnitudeEq := truncated
    have magnitudeValueEq := Option.some.inj magnitudeEq
    have nonnegative : 0 ≤ integer := by
      rw [← magnitudeValueEq]
      omega
    exact ⟨fun equal => by simp_all, fun _ => nonnegative⟩

/-- Both signed encodings of binary64 zero truncate to integer zero. -/
theorem binary64Truncate_signed_zero (negative : Bool) :
    binary64Truncate (UInt64.ofNat (if negative then 2^63 else 0)) = some 0 := by
  cases negative <;> decide

/-- Every binary64 number with a zero exponent or a biased exponent below
1023 has magnitude below one, so toward-zero conversion returns integer zero
regardless of sign or fraction payload. -/
theorem binary64Truncate_magnitude_below_one (bits : UInt64)
    (exponentBelowOne : binary64Exponent bits < 1023) :
    binary64Truncate bits = some 0 := by
  unfold binary64Truncate
  have notSpecial : binary64Exponent bits ≠ 2^11 - 1 := by omega
  simp only [if_neg notSpecial]
  have small : binary64Exponent bits = 0 ∨ binary64Exponent bits < 1023 :=
    Or.inr exponentBelowOne
  simp [small]

/-- Representative normal encodings confirm that the exponent arithmetic
uses the binary64 bias and returns exact integer results on either sign. -/
theorem binary64Truncate_one_bits :
    binary64Truncate (UInt64.ofNat (1023 * 2^52)) = some 1 := by decide

theorem binary64Truncate_negative_one_bits :
    binary64Truncate (UInt64.ofNat (2^63 + 1023 * 2^52)) = some (-1) := by decide

/-- The result is not restricted to machine-sized integers: a finite binary64
encoding of 2^64 converts to the corresponding arbitrary-precision `Int`. -/
theorem binary64Truncate_above_uint64_bits :
    binary64Truncate (UInt64.ofNat (1087 * 2^52)) = some (Int.ofNat (2^64)) := by decide

/-- For every finite binary64 value whose unbiased exponent is at least 52,
the fraction field and implicit leading bit form an integer significand, and
the exponent directly gives the exact left shift before applying the sign. -/
theorem binary64Truncate_large_finite
    (bits : UInt64) (exponent : Nat)
    (exponentEq : binary64Exponent bits = exponent)
    (large : 1075 ≤ exponent) (finite : exponent < 2^11 - 1) :
    binary64Truncate bits = some (if bits.toNat / 2^63 = 1 then
      -Int.ofNat ((2^52 + binary64Fraction bits) * 2^(exponent - 1075))
      else Int.ofNat ((2^52 + binary64Fraction bits) * 2^(exponent - 1075))) := by
  unfold binary64Truncate
  rw [exponentEq]
  have notSpecial : exponent ≠ 2^11 - 1 := by omega
  have notZero : exponent ≠ 0 := by omega
  have notBelowOne : ¬ exponent < 1023 := by omega
  simp [notSpecial, notZero, notBelowOne, large]

/-- For finite normal encodings with magnitude at least one but with a
fractional integer part, truncation is unsigned significand division by the
corresponding power of two, followed by the binary64 sign. -/
theorem binary64Truncate_normal_fractional
    (bits : UInt64) (exponent : Nat)
    (exponentEq : binary64Exponent bits = exponent)
    (normal : 1023 ≤ exponent) (fractional : exponent < 1075) :
    binary64Truncate bits = some (if bits.toNat / 2^63 = 1 then
      -Int.ofNat ((2^52 + binary64Fraction bits) / 2^(1075 - exponent))
      else Int.ofNat ((2^52 + binary64Fraction bits) / 2^(1075 - exponent))) := by
  unfold binary64Truncate
  rw [exponentEq]
  have notSpecial : exponent ≠ 2^11 - 1 := by omega
  have notZero : exponent ≠ 0 := by omega
  have notBelowOne : ¬ exponent < 1023 := by omega
  have notLarge : ¬ 1075 ≤ exponent := by omega
  simp [notSpecial, notZero, notBelowOne, notLarge, normal, fractional]

/-- Complete finite-binary64 case split for toward-zero conversion. Every
finite encoding either truncates to zero below unit magnitude, divides its
significand for exponents 1023 through 1074, or shifts it for exponents at
least 1075. -/
theorem binary64Truncate_finite_cases (bits : UInt64)
    (finite : binary64Exponent bits < 2^11 - 1) :
    binary64Truncate bits =
      if binary64Exponent bits < 1023 then some 0 else
      if binary64Exponent bits < 1075 then
        some (if bits.toNat / 2^63 = 1 then
          -Int.ofNat ((2^52 + binary64Fraction bits) /
            2^(1075 - binary64Exponent bits))
        else Int.ofNat ((2^52 + binary64Fraction bits) /
            2^(1075 - binary64Exponent bits)))
      else
        some (if bits.toNat / 2^63 = 1 then
          -Int.ofNat ((2^52 + binary64Fraction bits) *
            2^(binary64Exponent bits - 1075))
        else Int.ofNat ((2^52 + binary64Fraction bits) *
            2^(binary64Exponent bits - 1075))) := by
  by_cases belowOne : binary64Exponent bits < 1023
  · rw [binary64Truncate_magnitude_below_one bits belowOne]
    simp [belowOne]
  · by_cases fractional : binary64Exponent bits < 1075
    · rw [binary64Truncate_normal_fractional bits (binary64Exponent bits) rfl
        (by omega) fractional]
      simp [belowOne, fractional]
    · rw [binary64Truncate_large_finite bits (binary64Exponent bits) rfl
        (by omega) finite]
      simp [belowOne, fractional]

/-- Exhaustive semantic classification for every binary64 bit pattern: the
all-ones exponent is rejected, and every other exponent follows the finite
toward-zero case split above. -/
theorem binary64Truncate_all_cases (bits : UInt64) :
    (binary64Exponent bits = 2^11 - 1 ∧ binary64Truncate bits = none) ∨
    (binary64Exponent bits < 2^11 - 1 ∧
      binary64Truncate bits =
        if binary64Exponent bits < 1023 then some 0 else
        if binary64Exponent bits < 1075 then
          some (if bits.toNat / 2^63 = 1 then
            -Int.ofNat ((2^52 + binary64Fraction bits) /
              2^(1075 - binary64Exponent bits))
          else Int.ofNat ((2^52 + binary64Fraction bits) /
              2^(1075 - binary64Exponent bits)))
        else
          some (if bits.toNat / 2^63 = 1 then
            -Int.ofNat ((2^52 + binary64Fraction bits) *
              2^(binary64Exponent bits - 1075))
          else Int.ofNat ((2^52 + binary64Fraction bits) *
              2^(binary64Exponent bits - 1075)))) := by
  by_cases nonfinite : binary64Exponent bits = 2^11 - 1
  · exact Or.inl ⟨nonfinite, binary64Truncate_nonfinite bits nonfinite⟩
  · have exponentBound : binary64Exponent bits < 2^11 := by
      unfold binary64Exponent
      exact Nat.mod_lt _ (by omega)
    exact Or.inr ⟨by omega, binary64Truncate_finite_cases bits (by omega)⟩

/-- The truncation model rejects exactly the exponent-all-ones encodings,
covering every infinity sign and every NaN payload. -/
theorem binary64Truncate_none_iff_nonfinite (bits : UInt64) :
    binary64Truncate bits = none ↔ binary64Exponent bits = 2^11 - 1 := by
  constructor
  · intro rejected
    rcases binary64Truncate_all_cases bits with ⟨nonfinite, _⟩ | ⟨finite, _⟩
    · exact nonfinite
    · rw [binary64Truncate_finite_cases bits finite] at rejected
      by_cases belowOne : binary64Exponent bits < 1023
      · simp [belowOne] at rejected
      · by_cases fractional : binary64Exponent bits < 1075
        · simp [belowOne, fractional] at rejected
        · simp [belowOne, fractional] at rejected
  · exact binary64Truncate_nonfinite bits

/-- The signed truncating quotient always has the unsigned quotient of the
magnitudes. This isolates the rounding convention used by the C/GMP model. -/
theorem truncQuotient_natAbs (left right : Int) :
    (truncQuotient left right).natAbs = left.natAbs / right.natAbs := by
  let magnitude := left.natAbs / right.natAbs
  change (if (left < 0) = (right < 0) then Int.ofNat magnitude
    else -Int.ofNat magnitude).natAbs = magnitude
  by_cases sameSign : (left < 0) = (right < 0) <;>
    simp [sameSign, Int.natAbs_neg, Int.natAbs_ofNat]

/-- When dividend and divisor have the same sign, the truncating quotient is
nonnegative. This includes the zero-divisor helper result; the Option wrapper
still rejects division by zero. -/
theorem truncQuotient_nonneg_of_same_sign (left right : Int)
    (sameSign : (left < 0) = (right < 0)) :
    0 ≤ truncQuotient left right := by
  unfold truncQuotient
  rw [if_pos sameSign]
  exact Int.ofNat_nonneg _

/-- When dividend and divisor have opposite signs, the truncating quotient is
nonpositive, matching GMP's sign convention for `mpz_tdiv_q`. -/
theorem truncQuotient_nonpos_of_opposite_sign (left right : Int)
    (oppositeSigns : (left < 0) ≠ (right < 0)) :
    truncQuotient left right ≤ 0 := by
  unfold truncQuotient
  rw [if_neg oppositeSigns]
  change -(Int.ofNat (left.natAbs / right.natAbs)) ≤ 0
  have magnitudeNonneg : 0 ≤ Int.ofNat (left.natAbs / right.natAbs) :=
    Int.ofNat_nonneg _
  omega

private theorem ofNat_not_lt_zero (n : Nat) : ((Int.ofNat n) < 0) = False := by
  apply propext
  constructor
  · intro h
    exact (Int.not_lt.mpr (Int.ofNat_nonneg n)) h |>.elim
  · intro h
    exact h.elim

private theorem negSucc_lt_zero_true (n : Nat) : ((Int.negSucc n) < 0) = True := by
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    exact Int.negSucc_lt_zero n

/-- Explicit sign cases for the quotient make the zero-toward rounding
convention visible over Lean's canonical integer constructors. -/
theorem truncQuotient_ofNat_negSucc (a b : Nat) :
    truncQuotient (Int.ofNat a) (Int.negSucc b) = -Int.ofNat (a / (b + 1)) := by
  unfold truncQuotient
  have sign : ((Int.ofNat a < 0) = (Int.negSucc b < 0)) = False := by
    rw [ofNat_not_lt_zero, negSucc_lt_zero_true]
    simp
  rw [if_neg (by simpa using sign)]
  simp [Int.natAbs_ofNat, Int.natAbs_negSucc]

theorem truncQuotient_negSucc_ofNat (a b : Nat) :
    truncQuotient (Int.negSucc a) (Int.ofNat b) = -Int.ofNat ((a + 1) / b) := by
  unfold truncQuotient
  have sign : ((Int.negSucc a < 0) = (Int.ofNat b < 0)) = False := by
    rw [negSucc_lt_zero_true, ofNat_not_lt_zero]
    simp
  rw [if_neg (by simpa using sign)]
  simp [Int.natAbs_ofNat, Int.natAbs_negSucc]

theorem truncQuotient_negSucc_negSucc (a b : Nat) :
    truncQuotient (Int.negSucc a) (Int.negSucc b) = Int.ofNat ((a + 1) / (b + 1)) := by
  unfold truncQuotient
  have sign : ((Int.negSucc a < 0) = (Int.negSucc b < 0)) = True := by
    rw [negSucc_lt_zero_true, negSucc_lt_zero_true]
    simp
  rw [if_pos (by simpa using sign)]
  simp [Int.natAbs_ofNat, Int.natAbs_negSucc]

private theorem natRemainder_sub_div_mul (numerator denominator : Nat) :
    numerator - numerator / denominator * denominator = numerator % denominator := by
  have division := Nat.mod_add_div numerator denominator
  rw [Nat.mul_comm denominator (numerator / denominator)] at division
  omega

private theorem intOfNat_sub_mul (numerator quotient denominator : Nat)
    (bound : quotient * denominator ≤ numerator) :
    Int.ofNat numerator - Int.ofNat quotient * Int.ofNat denominator =
      Int.ofNat (numerator - quotient * denominator) := by
  have product : Int.ofNat quotient * Int.ofNat denominator =
      Int.ofNat (quotient * denominator) := (Int.ofNat_mul quotient denominator).symm
  rw [product]
  exact (Int.ofNat_sub bound).symm

private theorem intOfNat_remainder (numerator denominator : Nat) :
    Int.ofNat numerator - Int.ofNat (numerator / denominator) * Int.ofNat denominator =
      Int.ofNat (numerator % denominator) := by
  have division := Nat.mod_add_div numerator denominator
  rw [Nat.mul_comm denominator (numerator / denominator)] at division
  have bound : numerator / denominator * denominator ≤ numerator := by omega
  calc
    Int.ofNat numerator - Int.ofNat (numerator / denominator) * Int.ofNat denominator =
        Int.ofNat (numerator - numerator / denominator * denominator) :=
      intOfNat_sub_mul numerator (numerator / denominator) denominator bound
    _ = Int.ofNat (numerator % denominator) := by
      rw [natRemainder_sub_div_mul]

/-- For nonnegative operands, the raw truncating remainder has the Nat
remainder magnitude. The statement includes a zero divisor, where the raw
helper returns the dividend; `integerOptional` separately rejects that case. -/
theorem truncRemainder_natAbs_ofNat (numerator denominator : Nat) :
    (Int.ofNat numerator -
      truncQuotient (Int.ofNat numerator) (Int.ofNat denominator) * Int.ofNat denominator).natAbs =
      numerator % denominator := by
  have numeratorNotNegative : (Int.ofNat numerator < 0) = False := by
    apply propext
    constructor
    · intro negative
      exact (Int.not_lt.mpr (Int.ofNat_nonneg numerator)) negative |>.elim
    · intro impossible
      exact impossible.elim
  have denominatorNotNegative : (Int.ofNat denominator < 0) = False := by
    apply propext
    constructor
    · intro negative
      exact (Int.not_lt.mpr (Int.ofNat_nonneg denominator)) negative |>.elim
    · intro impossible
      exact impossible.elim
  have quotientEq : truncQuotient (Int.ofNat numerator) (Int.ofNat denominator) =
      Int.ofNat (numerator / denominator) := by
    unfold truncQuotient
    have sameSign : (Int.ofNat numerator < 0) = (Int.ofNat denominator < 0) := by
      rw [numeratorNotNegative, denominatorNotNegative]
    rw [if_pos sameSign]
    simp [Int.natAbs_ofNat]
  rw [quotientEq, intOfNat_remainder]
  change (Int.ofNat (numerator % denominator)).natAbs = numerator % denominator
  rfl

private theorem negSucc_eq_neg_ofNat (value : Nat) :
    Int.negSucc value = -Int.ofNat (value + 1) := by
  rw [Int.negSucc_eq]
  congr 1

/-- The raw truncating remainder has the magnitude of natural-number
remainder for every signed dividend and divisor. The zero-divisor helper case
is included (`Nat` remainder modulo zero is the dividend magnitude); the
Option-valued builtin still rejects that input. -/
theorem truncRemainder_natAbs (left right : Int) :
    (left - truncQuotient left right * right).natAbs = left.natAbs % right.natAbs := by
  cases left with
  | ofNat numerator =>
      cases right with
      | ofNat denominator => exact truncRemainder_natAbs_ofNat numerator denominator
      | negSucc denominator =>
          rw [truncQuotient_ofNat_negSucc, negSucc_eq_neg_ofNat, Int.neg_mul_neg]
          rw [intOfNat_remainder]
          rfl
  | negSucc numerator =>
      cases right with
      | ofNat denominator =>
          rw [truncQuotient_negSucc_ofNat, negSucc_eq_neg_ofNat, Int.neg_mul]
          rw [Int.sub_neg]
          have remainder := intOfNat_remainder (numerator + 1) denominator
          have reorder :
              -Int.ofNat (numerator + 1) +
                  Int.ofNat ((numerator + 1) / denominator) * Int.ofNat denominator =
                Int.ofNat ((numerator + 1) / denominator) * Int.ofNat denominator -
                  Int.ofNat (numerator + 1) := by omega
          rw [reorder, ← Int.neg_sub, remainder]
          simp only [Int.natAbs_neg, Int.natAbs_ofNat]
          rfl
      | negSucc denominator =>
          rw [truncQuotient_negSucc_negSucc, negSucc_eq_neg_ofNat,
            negSucc_eq_neg_ofNat, Int.mul_neg]
          rw [Int.sub_neg]
          have remainder := intOfNat_remainder (numerator + 1) (denominator + 1)
          have reorder :
              -Int.ofNat (numerator + 1) +
                  Int.ofNat ((numerator + 1) / (denominator + 1)) *
                    Int.ofNat (denominator + 1) =
                Int.ofNat ((numerator + 1) / (denominator + 1)) *
                    Int.ofNat (denominator + 1) - Int.ofNat (numerator + 1) := by omega
          rw [reorder, ← Int.neg_sub, remainder]
          simp only [Int.natAbs_neg, Int.natAbs_ofNat]
          rfl

/-- A defined remainder is strictly smaller in magnitude than its nonzero
divisor, the standard truncating-division remainder bound. -/
theorem truncRemainder_natAbs_lt (left right : Int) (rightNonzero : right ≠ 0) :
    (left - truncQuotient left right * right).natAbs < right.natAbs := by
  rw [truncRemainder_natAbs]
  exact Nat.mod_lt _ (Int.natAbs_pos.mpr rightNonzero)

private theorem truncQuotient_ofNat_ofNat (numerator denominator : Nat) :
    truncQuotient (Int.ofNat numerator) (Int.ofNat denominator) =
      Int.ofNat (numerator / denominator) := by
  unfold truncQuotient
  have numeratorNotNegative : (Int.ofNat numerator < 0) = False := by
    apply propext
    constructor
    · intro negative
      exact (Int.not_lt.mpr (Int.ofNat_nonneg numerator)) negative |>.elim
    · intro impossible
      exact impossible.elim
  have denominatorNotNegative : (Int.ofNat denominator < 0) = False := by
    apply propext
    constructor
    · intro negative
      exact (Int.not_lt.mpr (Int.ofNat_nonneg denominator)) negative |>.elim
    · intro impossible
      exact impossible.elim
  have sameSign : (Int.ofNat numerator < 0) = (Int.ofNat denominator < 0) := by
    rw [numeratorNotNegative, denominatorNotNegative]
  rw [if_pos sameSign]
  simp [Int.natAbs_ofNat]

/-- Exact signed remainder formulas over Lean's canonical integer
constructors. These equations retain the dividend sign of truncating `tdiv`.
-/
theorem truncRemainder_ofNat_ofNat (numerator denominator : Nat) :
    Int.ofNat numerator -
      truncQuotient (Int.ofNat numerator) (Int.ofNat denominator) * Int.ofNat denominator =
      Int.ofNat (numerator % denominator) := by
  rw [truncQuotient_ofNat_ofNat, intOfNat_remainder]

theorem truncRemainder_ofNat_negSucc (numerator denominator : Nat) :
    Int.ofNat numerator -
      truncQuotient (Int.ofNat numerator) (Int.negSucc denominator) *
        Int.negSucc denominator = Int.ofNat (numerator % (denominator + 1)) := by
  rw [truncQuotient_ofNat_negSucc, negSucc_eq_neg_ofNat, Int.neg_mul_neg,
    intOfNat_remainder]

theorem truncRemainder_negSucc_ofNat (numerator denominator : Nat) :
    Int.negSucc numerator -
      truncQuotient (Int.negSucc numerator) (Int.ofNat denominator) *
        Int.ofNat denominator = -Int.ofNat ((numerator + 1) % denominator) := by
  rw [truncQuotient_negSucc_ofNat, negSucc_eq_neg_ofNat, Int.neg_mul]
  rw [Int.sub_neg]
  have remainder := intOfNat_remainder (numerator + 1) denominator
  have reorder :
      -Int.ofNat (numerator + 1) +
          Int.ofNat ((numerator + 1) / denominator) * Int.ofNat denominator =
        Int.ofNat ((numerator + 1) / denominator) * Int.ofNat denominator -
          Int.ofNat (numerator + 1) := by omega
  rw [reorder, ← Int.neg_sub, remainder]

theorem truncRemainder_negSucc_negSucc (numerator denominator : Nat) :
    Int.negSucc numerator -
      truncQuotient (Int.negSucc numerator) (Int.negSucc denominator) *
        Int.negSucc denominator = -Int.ofNat ((numerator + 1) % (denominator + 1)) := by
  rw [truncQuotient_negSucc_negSucc, negSucc_eq_neg_ofNat,
    negSucc_eq_neg_ofNat, Int.mul_neg]
  rw [Int.sub_neg]
  have remainder := intOfNat_remainder (numerator + 1) (denominator + 1)
  have reorder :
      -Int.ofNat (numerator + 1) +
          Int.ofNat ((numerator + 1) / (denominator + 1)) *
            Int.ofNat (denominator + 1) =
        Int.ofNat ((numerator + 1) / (denominator + 1)) *
            Int.ofNat (denominator + 1) - Int.ofNat (numerator + 1) := by omega
  rw [reorder, ← Int.neg_sub, remainder]

/-- The sign of a truncating remainder follows its dividend, including the
zero remainder case. -/
theorem truncRemainder_sign (left right : Int) :
    (left < 0 → left - truncQuotient left right * right ≤ 0) ∧
      (0 ≤ left → 0 ≤ left - truncQuotient left right * right) := by
  cases left with
  | ofNat numerator =>
      cases right with
      | ofNat denominator =>
          rw [truncRemainder_ofNat_ofNat]
          exact ⟨fun h => (Int.not_lt.mpr (Int.ofNat_nonneg numerator)) h |>.elim,
            fun _ => Int.ofNat_nonneg _⟩
      | negSucc denominator =>
          rw [truncRemainder_ofNat_negSucc]
          exact ⟨fun h => (Int.not_lt.mpr (Int.ofNat_nonneg numerator)) h |>.elim,
            fun _ => Int.ofNat_nonneg _⟩
  | negSucc numerator =>
      cases right with
      | ofNat denominator =>
          rw [truncRemainder_negSucc_ofNat]
          exact ⟨fun _ => by
              have remainderNonneg : 0 ≤ Int.ofNat ((numerator + 1) % denominator) :=
                Int.ofNat_nonneg _
              omega,
            fun h => (Int.not_le.mpr (Int.negSucc_lt_zero numerator)) h |>.elim⟩
      | negSucc denominator =>
          rw [truncRemainder_negSucc_negSucc]
          exact ⟨fun _ => by
              have remainderNonneg : 0 ≤ Int.ofNat ((numerator + 1) % (denominator + 1)) :=
                Int.ofNat_nonneg _
              omega,
            fun h => (Int.not_le.mpr (Int.negSucc_lt_zero numerator)) h |>.elim⟩

/-- A truncating quotient is zero exactly when the unsigned magnitude
division is zero. This includes zero divisors, for which Nat division by zero
and the raw quotient helper both produce zero; the Option builtin still
rejects that case separately. -/
theorem truncQuotient_eq_zero_iff (left right : Int) :
    truncQuotient left right = 0 ↔ left.natAbs / right.natAbs = 0 := by
  constructor
  · intro quotientZero
    have magnitudeZero := congrArg Int.natAbs quotientZero
    rw [truncQuotient_natAbs] at magnitudeZero
    simpa using magnitudeZero
  · intro magnitudeZero
    have quotientMagnitudeZero : (truncQuotient left right).natAbs = 0 := by
      rw [truncQuotient_natAbs]
      exact magnitudeZero
    exact Int.natAbs_eq_zero.mp quotientMagnitudeZero

/-- Integer option-valued builtin semantics. Division by zero returns None;
remainder is defined from the same truncating quotient, matching `mpz_tdiv_r`
and fixing the remainder sign to the dividend. -/
def integerOptional (operation : Primitive) (left right : Int) : Option Int :=
  if right = 0 then none else
    match operation with
    | .quotient => some (truncQuotient left right)
    | .remainder => some (left - truncQuotient left right * right)
    | _ => none

theorem integerOptional_quotient_defined_iff (left right : Int) :
    (integerOptional .quotient left right).isSome = true ↔ right ≠ 0 := by
  by_cases h : right = 0 <;> simp [integerOptional, h]

theorem integerOptional_quotient_natAbs (left right : Int) (nonzero : right ≠ 0) :
    ∃ quotient, integerOptional .quotient left right = some quotient ∧
      quotient.natAbs = left.natAbs / right.natAbs := by
  refine ⟨truncQuotient left right, ?_, truncQuotient_natAbs left right⟩
  simp [integerOptional, nonzero]

/-- The Option-valued quotient result carries both its magnitude contract and
the dividend/divisor sign convention of truncating division. -/
theorem integerOptional_quotient_sign (left right : Int) (nonzero : right ≠ 0) :
    ∃ quotient, integerOptional .quotient left right = some quotient ∧
      (if (left < 0) = (right < 0) then 0 ≤ quotient else quotient ≤ 0) := by
  refine ⟨truncQuotient left right, ?_, ?_⟩
  · simp [integerOptional, nonzero]
  · by_cases sameSign : (left < 0) = (right < 0)
    · simp [sameSign]
      exact truncQuotient_nonneg_of_same_sign left right sameSign
    · simp [sameSign]
      exact truncQuotient_nonpos_of_opposite_sign left right sameSign

theorem integerOptional_remainder_defined_iff (left right : Int) :
    (integerOptional .remainder left right).isSome = true ↔ right ≠ 0 := by
  by_cases h : right = 0 <;> simp [integerOptional, h]

theorem integerOptional_remainder_equation (left right : Int) (nonzero : right ≠ 0) :
    integerOptional .remainder left right =
      some (left - truncQuotient left right * right) := by
  simp [integerOptional, nonzero]

/-- The Option-valued remainder builtin returns a value satisfying GMP's
strict magnitude bound whenever the divisor is nonzero. -/
theorem integerOptional_remainder_abs_bound (left right : Int)
    (nonzero : right ≠ 0) :
    ∃ remainder, integerOptional .remainder left right = some remainder ∧
      remainder.natAbs < right.natAbs := by
  refine ⟨left - truncQuotient left right * right, ?_, ?_⟩
  · exact integerOptional_remainder_equation left right nonzero
  · exact truncRemainder_natAbs_lt left right nonzero

/-- For every nonzero divisor, quotient and remainder are both present and
reconstruct the dividend with the C/GMP truncation convention. -/
theorem integerOptional_division_equation (left right : Int) (nonzero : right ≠ 0) :
    ∃ quotient remainder,
      integerOptional .quotient left right = some quotient ∧
      integerOptional .remainder left right = some remainder ∧
      left = quotient * right + remainder := by
  refine ⟨truncQuotient left right, left - truncQuotient left right * right,
    ?_, ?_, ?_⟩
  · simp [integerOptional, nonzero]
  · exact integerOptional_remainder_equation left right nonzero
  · calc
      left = left - truncQuotient left right * right + truncQuotient left right * right :=
        (Int.sub_add_cancel left (truncQuotient left right * right)).symm
      _ = truncQuotient left right * right +
          (left - truncQuotient left right * right) := Int.add_comm _ _

inductive Member : List Ty → Nat → Ty → Prop where
  | zero : Member (t :: Γ) 0 t
  | succ : Member Γ n t → Member (u :: Γ) (n + 1) t

inductive Var : List Ty → Ty → Type where
  | zero : Var (t :: Γ) t
  | succ : Var Γ t → Var (u :: Γ) t

def Var.index : Var Γ t → Nat
  | .zero => 0
  | .succ v => v.index + 1

theorem Var.member (v : Var Γ t) : Member Γ v.index t := by
  induction v with
  | zero => exact .zero
  | succ _ ih => exact .succ ih

inductive Expr : List Ty → Ty → Type where
  | var : Var Γ t → Expr Γ t
  | bool : Bool → Expr Γ .boolean
  | int : Int → Expr Γ .integer
  | unit : Expr Γ .unit
  | floatBits : UInt64 → Expr Γ .floating
  | str : String → Expr Γ .string
  | char : Char → Expr Γ .character
  | builtin (operation : Primitive) : Expr Γ operation.type
  | lam : Expr (a :: Γ) b → Expr Γ (.fn a b)
  | app : Expr Γ (.fn a b) → Expr Γ a → Expr Γ b
  | ite : Expr Γ .boolean → Expr Γ t → Expr Γ t → Expr Γ t
  | nil : Expr Γ (.list a)
  | cons : Expr Γ a → Expr Γ (.list a) → Expr Γ (.list a)
  | matchList : Expr Γ (.list a) → Expr Γ r → Expr (a :: .list a :: Γ) r → Expr Γ r
  | none : Expr Γ (.option a)
  | some : Expr Γ a → Expr Γ (.option a)
  | matchOption : Expr Γ (.option a) → Expr Γ r → Expr (a :: Γ) r → Expr Γ r
  | fix : Expr (t :: Γ) t → Expr Γ t

abbrev Ren (Γ Δ : List Ty) := {t : Ty} → Var Γ t → Var Δ t
abbrev Sub (Γ Δ : List Ty) := {t : Ty} → Var Γ t → Expr Δ t

def liftRen (rename : Ren Γ Δ) : Ren (a :: Γ) (a :: Δ) :=
  fun v => match v with
    | .zero => .zero
    | .succ w => .succ (rename w)

def Expr.rename (rename : Ren Γ Δ) : Expr Γ t → Expr Δ t
  | .var v => .var (rename v)
  | .bool b => .bool b
  | .int n => .int n
  | .unit => .unit
  | .floatBits bits => .floatBits bits
  | .str s => .str s
  | .char c => .char c
  | .builtin operation => .builtin operation
  | .lam body => .lam (body.rename (liftRen rename))
  | .app f x => .app (f.rename rename) (x.rename rename)
  | .ite c yes no => .ite (c.rename rename) (yes.rename rename) (no.rename rename)
  | .nil => .nil
  | .cons head tail => .cons (head.rename rename) (tail.rename rename)
  | .matchList scrut empty full =>
      .matchList (scrut.rename rename) (empty.rename rename)
        (full.rename (liftRen (liftRen rename)))
  | .none => .none
  | .some value => .some (value.rename rename)
  | .matchOption scrut empty full =>
      .matchOption (scrut.rename rename) (empty.rename rename) (full.rename (liftRen rename))
  | .fix body => .fix (body.rename (liftRen rename))

def liftSub (substitution : Sub Γ Δ) : Sub (a :: Γ) (a :: Δ) :=
  fun v => match v with
    | .zero => .var .zero
    | .succ w => (substitution w).rename (fun x => .succ x)

def Expr.subst (substitution : Sub Γ Δ) : Expr Γ t → Expr Δ t
  | .var v => substitution v
  | .bool b => .bool b
  | .int n => .int n
  | .unit => .unit
  | .floatBits bits => .floatBits bits
  | .str s => .str s
  | .char c => .char c
  | .builtin operation => .builtin operation
  | .lam body => .lam (body.subst (liftSub substitution))
  | .app f x => .app (f.subst substitution) (x.subst substitution)
  | .ite c yes no => .ite (c.subst substitution) (yes.subst substitution) (no.subst substitution)
  | .nil => .nil
  | .cons head tail => .cons (head.subst substitution) (tail.subst substitution)
  | .matchList scrut empty full =>
      .matchList (scrut.subst substitution) (empty.subst substitution)
        (full.subst (liftSub (liftSub substitution)))
  | .none => .none
  | .some value => .some (value.subst substitution)
  | .matchOption scrut empty full =>
      .matchOption (scrut.subst substitution) (empty.subst substitution)
        (full.subst (liftSub substitution))
  | .fix body => .fix (body.subst (liftSub substitution))

def singleHoleSub (value : Expr Γ a) : Sub [a] Γ :=
  fun | .zero => value

def Expr.add (left right : Expr Γ .integer) : Expr Γ .integer :=
  .app (.app (.builtin .add) left) right

/- The erased term retains literal data and primitive identities, but its
type is not an index. HasType is an extrinsic typing derivation for it. -/
inductive Term where
  | var : Nat → Term
  | bool : Bool → Term
  | int : Int → Term
  | unit : Term
  | floatBits : UInt64 → Term
  | str : String → Term
  | char : Char → Term
  | builtin : Primitive → Term
  | lam : Term → Term
  | app : Term → Term → Term
  | ite : Term → Term → Term → Term
  | nil : Term
  | cons : Term → Term → Term
  | matchList : Term → Term → Term → Term
  | none : Term
  | some : Term → Term
  | matchOption : Term → Term → Term → Term
  | fix : Term → Term

inductive HasType : List Ty → Term → Ty → Prop where
  | var : Member Γ index t → HasType Γ (.var index) t
  | bool : HasType Γ (.bool b) .boolean
  | int : HasType Γ (.int n) .integer
  | unit : HasType Γ .unit .unit
  | floatBits : HasType Γ (.floatBits bits) .floating
  | str : HasType Γ (.str s) .string
  | char : HasType Γ (.char c) .character
  | builtin : HasType Γ (.builtin operation) operation.type
  | lam : HasType (a :: Γ) body b → HasType Γ (.lam body) (.fn a b)
  | app : HasType Γ f (.fn a b) → HasType Γ x a → HasType Γ (.app f x) b
  | ite : HasType Γ c .boolean → HasType Γ yes t → HasType Γ no t → HasType Γ (.ite c yes no) t
  | nil : HasType Γ .nil (.list a)
  | cons : HasType Γ head a → HasType Γ tail (.list a) → HasType Γ (.cons head tail) (.list a)
  | matchList : HasType Γ scrut (.list a) → HasType Γ empty r →
      HasType (a :: .list a :: Γ) full r → HasType Γ (.matchList scrut empty full) r
  | none : HasType Γ .none (.option a)
  | some : HasType Γ value a → HasType Γ (.some value) (.option a)
  | matchOption : HasType Γ scrut (.option a) → HasType Γ empty r →
      HasType (a :: Γ) full r → HasType Γ (.matchOption scrut empty full) r
  | fix : HasType (t :: Γ) body t → HasType Γ (.fix body) t

def Expr.erase : Expr Γ t → Term
  | .var v => .var v.index
  | .bool b => .bool b
  | .int n => .int n
  | .unit => .unit
  | .floatBits bits => .floatBits bits
  | .str s => .str s
  | .char c => .char c
  | .builtin operation => .builtin operation
  | .lam body => .lam body.erase
  | .app f x => .app f.erase x.erase
  | .ite c yes no => .ite c.erase yes.erase no.erase
  | .nil => .nil
  | .cons head tail => .cons head.erase tail.erase
  | .matchList scrut empty full => .matchList scrut.erase empty.erase full.erase
  | .none => .none
  | .some value => .some value.erase
  | .matchOption scrut empty full => .matchOption scrut.erase empty.erase full.erase
  | .fix body => .fix body.erase

theorem Expr.hasType (expression : Expr Γ t) : HasType Γ expression.erase t := by
  induction expression with
  | var v => exact .var v.member
  | bool => exact .bool
  | int => exact .int
  | unit => exact .unit
  | floatBits => exact .floatBits
  | str => exact .str
  | char => exact .char
  | builtin => exact .builtin
  | lam _ ih => exact .lam ih
  | app _ _ ihf ihx => exact .app ihf ihx
  | ite _ _ _ ihc ihy ihn => exact .ite ihc ihy ihn
  | nil => exact .nil
  | cons _ _ ihh iht => exact .cons ihh iht
  | matchList _ _ _ ihs ihe ihf => exact .matchList ihs ihe ihf
  | none => exact .none
  | some _ ih => exact .some ih
  | matchOption _ _ _ ihs ihe ihf => exact .matchOption ihs ihe ihf
  | fix _ ih => exact .fix ih

/-- Typed substitution preserves the extrinsic typing certificate of the
erased syntax consumed by the independent checker. The substitution may map
each source variable to an arbitrary typed expression in a different target
context; its type index is fixed by `Sub`. -/
theorem Expr.subst_hasType (expression : Expr Γ t) (substitution : Sub Γ Δ) :
    HasType Δ (expression.subst substitution).erase t :=
  (expression.subst substitution).hasType

/-- Specialization for macro contracts that replace one typed hole. This
connects an intrinsically typed replacement expression to the checker-facing
`Term` typing evidence after substitution. -/
theorem Expr.singleHoleSubstitution_hasType (body : Expr [a] result)
    (replacement : Expr Γ a) :
    HasType Γ (body.subst (singleHoleSub replacement)).erase result :=
  Expr.subst_hasType body (singleHoleSub replacement)

/-- A typed macro contract with any finite number of typed holes. The body
records the type of every argument in its context, so a substitution cannot
change the contract's result type. -/
structure MacroContract (arguments : List Ty) (result : Ty) where
  body : Expr arguments result

namespace MacroContract

/-- Instantiate a typed contract with a replacement expression. -/
def instantiate (contract : MacroContract arguments result)
    (substitution : Sub arguments Γ) : Expr Γ result :=
  contract.body.subst substitution

/-- The expansion produced by a typed macro contract retains its result type
in both the intrinsic representation and the independent erased checker. -/
theorem instantiate_hasType (contract : MacroContract arguments result)
    (substitution : Sub arguments Γ) :
    HasType Γ (contract.instantiate substitution).erase result :=
  Expr.subst_hasType contract.body substitution

end MacroContract

end NLisp.TypedExpansion
