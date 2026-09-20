"""Integer model adapters versus pinned source decoders under explicit policies.

Flocq has no Lean Float.Model export. The bridge compares its actual bit
decoders with explicit NaN canonicalization and UInt wrapping only on the
routes that perform those conversions. Raw source Z decoding uses a sign
threshold, not modulo-word sign extraction outside its bounded-word domain.
"""
from contextlib import contextmanager
from dataclasses import asdict, dataclass
import random

import flocq_bridge as bridge

OPERATION = "model_adapters"
COLUMNS = ("source.raw", "source.to_model", "word_model.to_source",
           "word_model.source_model_roundtrip", "source.model_source_roundtrip")


@dataclass(frozen=True)
class Case:
    op: str
    args: tuple[int, ...]

    def __post_init__(self):
        if self.op != OPERATION or len(self.args) != 2:
            raise ValueError("model adapter cases require model_adapters and width/integer arguments")
        if any(type(value) is not int for value in self.args):
            raise ValueError("model adapter inputs must be integers")
        if self.args[0] not in (32, 64):
            raise ValueError("model adapter width must be 32 or 64")


def expressions(case):
    width, bits = case.args
    return (f"modelAdapterObserve{width} ({bits})",
            f"modelAdapterObserve{width} ({bits}%Z)")


def corpus(seed, samples):
    cases = []
    for width, mantissa, exponent in ((32, 23, 8), (64, 52, 11)):
        modulus = 1 << width
        maximum = (1 << exponent) - 1
        bias = maximum // 2
        for sign in (0, 1):
            for e in (0, 1, 2, 3, bias-1, bias, bias+1, maximum-2, maximum-1, maximum):
                for fraction in (0, 1, 1 << (mantissa-1), (1 << mantissa)-1):
                    word = (sign << (width-1)) + (e << mantissa) + fraction
                    for value in (word, word-modulus, word+modulus, word+modulus**2):
                        cases.append(Case(OPERATION, (width, value)))
    rng = random.Random(seed)
    for _ in range(samples):
        width = rng.choice((32, 64))
        size = rng.choice((width-1, width, width+1, 192))
        value = rng.getrandbits(size) * rng.choice((-1, 1))
        cases.append(Case(OPERATION, (width, value)))
    return cases


def expected(case):
    width, bits = case.args
    mantissa, exponent = (23, 8) if width == 32 else (52, 11)
    sign_weight = 2 ** (width-1)
    source_word = bits % sign_weight + (sign_weight if bits >= sign_weight else 0)
    wrapped_word = bits % (2 ** width)

    def canonical(word):
        field, fraction = divmod(word, 2 ** mantissa)
        if field % (2 ** exponent) == 2 ** exponent-1 and fraction != 0:
            return (2 ** exponent-1) * 2 ** mantissa + 2 ** (mantissa-1)
        return word

    source_model, word_model = canonical(source_word), canonical(wrapped_word)
    return [source_word, source_model, word_model, word_model, source_model]


def independent_checks(case, row):
    if len(row) != len(COLUMNS) or any(type(value) is not int for value in row):
        raise ValueError("model adapter oracle requires five integer observations")
    wanted = expected(case)
    for column, (actual, target) in enumerate(zip(row, wanted, strict=True)):
        if actual != target:
            raise AssertionError(f"model adapter oracle {COLUMNS[column]} failed for {asdict(case)}: "
                                 f"actual={actual}, expected={target}")
    return len(COLUMNS)


LEAN_HEADER = """import FloatSpec.Test.NativeModelAdapters
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option pp.maxSteps 200000
set_option pp.deepTerms true
namespace Bridge
def modelAdapterObserve32 := FloatSpec.Test.NativeModelAdapters.observe32
def modelAdapterObserve64 := FloatSpec.Test.NativeModelAdapters.observe64
"""
COQ_HEADER = (bridge.ROOT / "scripts/fixtures/NativeModelAdapters.v").read_text().split("Example ")[0]


@contextmanager
def profile():
    metadata = {"name": "Lean logical-model adapters through pinned Flocq bit decoders",
                "columns": COLUMNS, "source_exports": ["b32_of_bits", "b64_of_bits", "bits_of_b32", "bits_of_b64"],
                "adapter_policy": "model routes canonicalize NaNs; UInt routes wrap; raw source Z sign uses threshold",
                "native_float_ffi": False, "oracle_checked_cases": 0,
                "oracle_assertions": 0, "out_of_range_cases": 0, "distinct_route_cases": 0}
    original_compare = bridge.compare

    def compare(cases, observations):
        mismatches = original_compare(cases, observations)
        if not mismatches:
            for case, row in zip(cases, observations["compiled"], strict=True):
                try:
                    count = independent_checks(case, row)
                except Exception:
                    metadata["oracle_failure_case"] = asdict(case)
                    raise
                metadata["oracle_checked_cases"] += 1
                metadata["oracle_assertions"] += count
                width, bits = case.args
                metadata["out_of_range_cases"] += not (0 <= bits < 2 ** width)
                metadata["distinct_route_cases"] += row[1] != row[2]
        return mismatches

    overrides = {"OPS": (OPERATION,), "ARITIES": {OPERATION: 2},
                 "WIDTHS": {OPERATION: len(COLUMNS)}, "RADIX_OPS": set(),
                 "BATCH_LIMITS": {OPERATION: 25}, "Case": Case,
                 "LEAN_HEADER": LEAN_HEADER, "COQ_HEADER": COQ_HEADER,
                 "expressions": expressions, "corpus": corpus, "compare": compare}
    previous = {name: getattr(bridge, name) for name in overrides}
    try:
        for name, replacement in overrides.items():
            setattr(bridge, name, replacement)
        yield metadata
    finally:
        for name, original in previous.items():
            setattr(bridge, name, original)


def main():
    with profile() as metadata:
        bridge.main(lean_build_targets=("FloatSpec.Test.NativeModelAdapters",),
                    profile_metadata=metadata)


if __name__ == "__main__":
    main()
