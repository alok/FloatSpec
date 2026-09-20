"""Independent finite-input IEEE oracle using exact rational/integer arithmetic.

This is not a translation of Flocq's integer algorithms. It selects points on
the representable grid, including midpoint and overflow boundaries. NaN and
infinite-input arithmetic are deliberately outside this oracle's scope.
"""

from dataclasses import dataclass
from fractions import Fraction
from math import isqrt


@dataclass(frozen=True)
class Format:
    fraction_bits: int
    exponent_bits: int

    def __post_init__(self):
        if self.fraction_bits < 1 or self.exponent_bits < 2:
            raise ValueError("need positive fraction width and at least two exponent bits")

    @property
    def bias(self):
        return (1 << (self.exponent_bits - 1)) - 1

    @property
    def width(self):
        return self.fraction_bits + self.exponent_bits + 1

    @property
    def sign_bit(self):
        return 1 << (self.width - 1)

    @property
    def infinity(self):
        return ((1 << self.exponent_bits) - 1) << self.fraction_bits

    @property
    def minimum_exponent(self):
        return 1 - self.bias - self.fraction_bits


FORMATS = {32: Format(23, 8), 64: Format(52, 11)}


def power_two(exponent):
    return Fraction(1 << exponent) if exponent >= 0 else Fraction(1, 1 << -exponent)


def floor_log_two(value):
    """Exact binary magnitude; no floating point or logarithms are used."""
    if value <= 0:
        raise ValueError("magnitude requires a positive rational")
    exponent = value.numerator.bit_length() - value.denominator.bit_length()
    return exponent - int(value < power_two(exponent))


def decode(fmt, word):
    """Return an exact finite value, or None for an infinity/NaN word."""
    if type(word) is not int or not 0 <= word < 1 << fmt.width:
        raise ValueError("word outside the requested IEEE width")
    exponent = (word & (fmt.sign_bit - 1)) >> fmt.fraction_bits
    fraction = word & ((1 << fmt.fraction_bits) - 1)
    if exponent == (1 << fmt.exponent_bits) - 1:
        return None
    mantissa = fraction + ((1 << fmt.fraction_bits) if exponent else 0)
    value = mantissa * power_two((exponent or 1) - fmt.bias - fmt.fraction_bits)
    return -value if word & fmt.sign_bit else value


def increment(mode, negative, lower, midpoint_comparison, exact):
    """Choose between consecutive grid points; mode order is NE,ZR,DN,UP,NA."""
    if mode not in range(5):
        raise ValueError("rounding mode must be in 0..4")
    if exact:
        return False
    if mode == 0:
        return midpoint_comparison > 0 or (midpoint_comparison == 0 and lower % 2 == 1)
    if mode == 4:
        return midpoint_comparison >= 0
    return (mode == 2 and negative) or (mode == 3 and not negative)


def encode_grid(fmt, negative, exponent, mantissa, mode):
    """Encode a selected grid point, applying the directed overflow policy."""
    if mantissa >= 1 << (fmt.fraction_bits + 1):
        mantissa //= 2
        exponent += 1
    exponent_field = exponent + fmt.fraction_bits + fmt.bias
    if exponent_field >= (1 << fmt.exponent_bits) - 1:
        to_infinity = mode in (0, 4) or (mode == 2 and negative) or (mode == 3 and not negative)
        magnitude = fmt.infinity if to_infinity else fmt.infinity - 1
    elif mantissa < 1 << fmt.fraction_bits:
        magnitude = mantissa
    else:
        magnitude = (exponent_field << fmt.fraction_bits) | (mantissa - (1 << fmt.fraction_bits))
    return magnitude | (fmt.sign_bit if negative else 0)


def round_rational(fmt, mode, value, negative_zero=False):
    """Round an exact rational by choosing between neighboring grid points."""
    if mode not in range(5):
        raise ValueError("rounding mode must be in 0..4")
    value = Fraction(value)
    if not value:
        return fmt.sign_bit if negative_zero else 0
    negative, magnitude = value < 0, abs(value)
    exponent = max(floor_log_two(magnitude) - fmt.fraction_bits, fmt.minimum_exponent)
    scaled = magnitude / power_two(exponent)
    lower, remainder = divmod(scaled.numerator, scaled.denominator)
    upper = increment(mode, negative, lower, 2 * remainder - scaled.denominator, remainder == 0)
    return encode_grid(fmt, negative, exponent, lower + upper, mode)


def round_sqrt(fmt, mode, value, negative_zero=False):
    """Compare squared integer midpoints; never approximate an irrational root."""
    value = Fraction(value)
    if mode not in range(5) or value < 0:
        raise ValueError("square-root oracle requires nonnegative input and a valid mode")
    if not value:
        return fmt.sign_bit if negative_zero else 0
    exponent = max(floor_log_two(value) // 2 - fmt.fraction_bits, fmt.minimum_exponent)
    scaled_square = value / power_two(2 * exponent)
    numerator, denominator = scaled_square.numerator, scaled_square.denominator
    lower = isqrt(numerator // denominator)
    exact = lower * lower * denominator == numerator
    midpoint = 4 * numerator - denominator * (2 * lower + 1) ** 2
    upper = increment(mode, False, lower, midpoint, exact)
    return encode_grid(fmt, False, exponent, lower + upper, mode)


def expected_operations(width, mode, left, right, third=None):
    """Expected words for operations whose operands are finite and in scope.

    Division by zero and negative square root are excluded. Signed zeros,
    overflow, gradual underflow, and all five rounding modes are included.
    """
    fmt = FORMATS[width]
    x, y = decode(fmt, left), decode(fmt, right)
    sx, sy = bool(left & fmt.sign_bit), bool(right & fmt.sign_bit)
    result = {}
    if x is not None and y is not None:
        for name, rhs, sign_rhs in (("add", y, sy), ("sub", -y, not sy)):
            zero_sign = sx if x == 0 and rhs == 0 and sx == sign_rhs else mode == 2
            result[name] = round_rational(fmt, mode, x + rhs, zero_sign)
        result["mul"] = round_rational(fmt, mode, x * y, sx != sy)
        if y:
            result["div"] = round_rational(fmt, mode, x / y, sx != sy)
        if third is not None:
            z = decode(fmt, third)
            if z is not None:
                product_sign, sz = sx != sy, bool(third & fmt.sign_bit)
                zero_sign = product_sign if x * y == 0 and z == 0 and product_sign == sz else mode == 2
                result["fma"] = round_rational(fmt, mode, x * y + z, zero_sign)
    if x is not None and x >= 0:
        result["sqrt_left"] = round_sqrt(fmt, mode, x, sx)
    return result


def standard_fields(width, word):
    """Canonical SingleNaN fields for an expected IEEE word."""
    fmt = FORMATS[width]
    sign = int(bool(word & fmt.sign_bit))
    exponent = (word & (fmt.sign_bit - 1)) >> fmt.fraction_bits
    fraction = word & ((1 << fmt.fraction_bits) - 1)
    if exponent == (1 << fmt.exponent_bits) - 1:
        return [2, 0, 0, 0] if fraction else [1, sign, 0, 0]
    if not exponent and not fraction:
        return [0, sign, 0, 0]
    return [3, sign, fraction + ((1 << fmt.fraction_bits) if exponent else 0),
            (exponent or 1) - fmt.bias - fmt.fraction_bits]


def mode_columns(case):
    """Independently check input echoes, six results, and both SingleNaN routes."""
    width, mode, left, right, third = case
    result = {"left": left, "right": right, "third": third}
    operations = expected_operations(width, mode, left, right, third)
    result.update(operations)
    for name, word in operations.items():
        for api in ("single", "source_single"):
            for field, value in zip(("kind", "sign", "mantissa", "exponent"),
                                    standard_fields(width, word), strict=True):
                result[f"{api}_{name}_{field}"] = value
    return result


def native_columns(case):
    """Native adapter canonicalizes NaNs; expected finite arithmetic is exact."""
    left, right = case

    def canonical(word):
        magnitude = word & ((1 << 63) - 1)
        return 0x7ff8000000000000 if magnitude > 0x7ff0000000000000 else word

    return {"left": canonical(left), "right": canonical(right),
            **expected_operations(64, 0, left, right)}


def compare_columns(cases, observations, columns, expected_columns):
    """Return replayable mismatches and the number of independent field checks."""
    if not observations or len(columns) != len(set(columns)):
        raise ValueError("need observation paths and unique columns")
    if any(len(rows) != len(cases) or any(len(row) != len(columns) for row in rows)
           for rows in observations.values()):
        raise ValueError("incomplete exact-oracle observations")
    mismatches, assertions = [], 0
    for index, case in enumerate(cases):
        expected = expected_columns(case)
        if not expected.keys() <= set(columns):
            raise ValueError("oracle expected a column that is not observed")
        for path, rows in observations.items():
            wrong = [name for column, name in enumerate(columns)
                     if name in expected and rows[index][column] != expected[name]]
            assertions += len(expected)
            if wrong:
                mismatches.append({"case": case, "path": f"{path}-versus-exact-oracle",
                                   "columns": wrong,
                                   "expected": {name: expected[name] for name in wrong},
                                   "actual": {name: rows[index][columns.index(name)] for name in wrong}})
    return mismatches, assertions
