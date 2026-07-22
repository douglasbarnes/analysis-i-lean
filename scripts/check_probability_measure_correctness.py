#!/usr/bin/env python3
"""Source-pinned correctness audit for Probability and Measure."""
from __future__ import annotations

import argparse
import hashlib
import pathlib
import re
import sys
import urllib.request
from dataclasses import dataclass

ROOT = pathlib.Path(__file__).resolve().parents[1]
COURSE = ROOT / "ProbabilityAndMeasure"
SURFACE = COURSE / "CorrectnessAudit.lean"
SOURCE_REPOSITORY = "dalcde/cam-notes"
SOURCE_COMMIT_SHA = "0c1046b9244d84f65df513b14f22d26c51fd78b5"
SOURCE_PATH = "II_M/probability_and_measure.tex"
SOURCE_BLOB_SHA = "c438fb5a8355273970359a6e5731c573afc510b4"
SOURCE_URL = f"https://raw.githubusercontent.com/{SOURCE_REPOSITORY}/{SOURCE_COMMIT_SHA}/{SOURCE_PATH}"
EXPECTED_LABELLED = 167
EXPECTED_THEOREM_LIKE = 93
THEOREM_KINDS = {"thm", "prop", "lemma", "cor"}

# FULL means the declaration proves every clause, or a genuine generalisation from which it follows
# directly. Multiple names are allowed when the source environment has several clauses.
FULL: dict[int, tuple[str, ...]] = {
    10: ("dynkin_pi_system_source",),
    17: ("finite_measure_uniqueness_source",),
    23: ("lebesgue_measure_translation_source",),
    31: ("independent_events_generated_sigma_source",),
    32: ("independent_generated_piSystems_source",),
    34: ("borelCantelli_first_source",),
    35: ("borelCantelli_second_source",),
    37: ("source037_measurable_generateFrom",),
    40: ("source040_measurable_pi_iff",),
    41: ("source041_measurable_operations",),
    49: ("source049_cdf_properties",),
    51: ("source051_realize_distribution_function",),
    58: ("source058_tendstoInMeasure_of_tendsto_ae", "source058_exists_subsequence_tendsto_ae"),
    62: ("source062_kolmogorov_zero_one", "source062_tail_measurable_ae_constant"),
    64: ("source064_simple_function_iff",),
    68: ("monotone_convergence_source",),
    69: ("source069_lintegral_properties",),
    70: ("source070_integral_properties",),
    71: ("source071_ae_eq_zero_of_piSystem_setIntegral_zero",),
    72: ("source072_lintegral_tsum",),
    73: ("source073_fatou",),
    76: ("source076_restrict_is_measure",),
    77: ("source077_restrict_measurable",),
    78: ("source078_restrict_integrable",),
    80: ("source080_lintegral_map",),
    82: ("source082_pushforward_is_measure",),
    87: ("measurable_product_section_source", "measurable_product_section_symm_source"),
    92: ("source092_markov",),
    94: ("jensen_source",),
    98: ("add_rpow_bound_source",),
    99: ("minkowski_eLpNorm_source",),
    104: ("lp_complete_source",),
    110: ("pythagoras_source",),
    111: ("parallelogram_source",),
    119: ("source119_uniformIntegrable_iff_tail",),
    120: ("source120_finite_uniformIntegrable",),
    131: ("characteristic_function_convolution_source",),
    134: ("gaussian_characteristic_function_source",),
    144: ("plancherel_source",),
    145: ("fourier_l2_equiv_source",),
    146: ("characteristic_function_unique_source",),
    150: ("levy_convergence_source",),
    152: ("gaussian_mean_source", "gaussian_variance_source", "gaussian_affine_source", "gaussian_characteristic_function_source"),
    166: ("strong_law_source",),
    167: ("central_limit_source",),
}

# PARTIAL has a real compiled declaration, but a source clause, direction, or hypothesis conversion
# remains to be formalised.
PARTIAL: dict[int, tuple[tuple[str, ...], str]] = {
    7: (("dynkin_intersections_form_sigma_source",), "only the nontrivial Dynkin-plus-intersections direction is packaged"),
    16: (("caratheodory_extension_source",), "uses sigma-subadditivity of AddContent; the source's countable-additivity-to-extension reduction is not packaged"),
    20: (("lebesgue_measure_exists_unique_source",), "uniqueness is stated among locally finite measures and on open intervals"),
    46: (("source046_stieltjes_measure_exists", "source046_stieltjes_measure_unique"), "existence and uniqueness for a given Stieltjes function are formalised; the converse representation of every nonzero Radon measure remains"),
    74: (("dominated_convergence_source",), "current wrapper is the nonnegative ENNReal version, not the signed Bochner statement"),
    88: (("product_measure_rectangle_source",), "rectangle evaluation is proved, but existence and uniqueness are not packaged in one declaration"),
    89: (("fubini_source", "fubini_swap_source"), "Bochner Fubini is present; the full Tonelli and converse-integrability clauses remain"),
    97: (("holder_source",), "current wrapper is for nonnegative ENNReal functions; the real absolute-value form remains to be derived"),
    117: (("source117_uniformIntegrable_sum",), "binary union closure is proved; an explicit finite-family induction theorem remains"),
    121: (("source121_vitali_with_integrable_limit", "source121_limit_integrable_of_UI_and_probability"), "the exact Mathlib Vitali equivalence and the derivation of integrability of the limit are proved; the source's full UniformIntegrable packaging in the L1-to-probability direction remains"),
    125: (("characteristic_function_bound_source",), "the finite-measure characteristic-function bound is present; the L1 Fourier bound remains"),
    126: (("characteristic_function_measurable_source",), "measurability is present, but the source states continuity"),
    132: (("fourier_inversion_source",), "current theorem gives inversion at continuity points; the source a.e. formulation remains"),
    164: (("von_neumann_mean_ergodic_source",), "Hilbert-space contraction theorem is present; the Koopman Lp formulation remains"),
}

@dataclass(frozen=True)
class Environment:
    source_id: int
    kind: str
    line_start: int
    line_end: int


def git_blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def line_starts(text: str) -> list[int]:
    starts = [0]
    starts.extend(m.end() for m in re.finditer(r"\n", text))
    return starts


def extract(text: str) -> list[Environment]:
    starts = line_starts(text)

    def line_no(offset: int) -> int:
        import bisect
        return bisect.bisect_right(starts, offset)

    pattern = re.compile(r"\\begin\{(defi|thm|prop|lemma|cor|notation)\}(?:\[[^\n]*?\])?")
    matches = list(pattern.finditer(text))
    out: list[Environment] = []
    for zero_index, match in enumerate(matches):
        kind = match.group(1)
        close = re.search(rf"\\end\{{{kind}\}}", text[match.end():])
        if close is None:
            raise RuntimeError(f"missing end for {kind} at line {line_no(match.start())}")
        end = match.end() + close.end()
        out.append(Environment(zero_index + 1, kind, line_no(match.start()), line_no(end)))
    return out


def read_source(path: pathlib.Path | None) -> str:
    if path is not None:
        data = path.read_bytes()
    else:
        with urllib.request.urlopen(SOURCE_URL) as response:
            data = response.read()
    actual = git_blob_sha(data)
    if actual != SOURCE_BLOB_SHA:
        raise RuntimeError(f"source blob mismatch: expected {SOURCE_BLOB_SHA}, got {actual}")
    return data.decode("utf-8")


def checked_names() -> set[str]:
    text = SURFACE.read_text(encoding="utf-8")
    return set(re.findall(r"#check\s+ProbabilityAndMeasure\.([A-Za-z0-9_']+)", text))


def scan_proof_escapes() -> list[str]:
    errors: list[str] = []
    patterns = {
        "sorry": re.compile(r"(?m)^\s*sorry\b"),
        "admit": re.compile(r"(?m)^\s*admit\b"),
        "axiom": re.compile(r"(?m)^\s*axiom\b"),
        "opaque": re.compile(r"(?m)^\s*opaque\b"),
    }
    for path in sorted(COURSE.glob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for label, pattern in patterns.items():
            if pattern.search(text):
                errors.append(f"{path.relative_to(ROOT)} contains {label}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--baseline", action="store_true")
    mode.add_argument("--strict", action="store_true")
    parser.add_argument("--source-file", type=pathlib.Path)
    args = parser.parse_args()

    envs = extract(read_source(args.source_file))
    if len(envs) != EXPECTED_LABELLED:
        raise RuntimeError(f"expected {EXPECTED_LABELLED} labelled environments, found {len(envs)}")
    theorem_envs = [e for e in envs if e.kind in THEOREM_KINDS]
    if len(theorem_envs) != EXPECTED_THEOREM_LIKE:
        raise RuntimeError(f"expected {EXPECTED_THEOREM_LIKE} theorem-like environments, found {len(theorem_envs)}")
    theorem_ids = {e.source_id for e in theorem_envs}
    if not set(FULL) <= theorem_ids or not set(PARTIAL) <= theorem_ids:
        raise RuntimeError("coverage map contains non-theorem source IDs")
    overlap = set(FULL) & set(PARTIAL)
    if overlap:
        raise RuntimeError(f"IDs classified both full and partial: {sorted(overlap)}")

    checked = checked_names()
    expected_names = {name for names in FULL.values() for name in names}
    expected_names |= {name for names, _ in PARTIAL.values() for name in names}
    missing_checks = sorted(expected_names - checked)
    if missing_checks:
        raise RuntimeError("correctness surface is missing #check entries: " + ", ".join(missing_checks))

    proof_errors = scan_proof_escapes()
    if proof_errors:
        raise RuntimeError("; ".join(proof_errors))

    unmapped = theorem_ids - set(FULL) - set(PARTIAL)
    print(f"Probability and Measure correctness audit: {len(FULL)} full / {len(PARTIAL)} partial / {len(unmapped)} unmapped")
    print("full IDs:", ", ".join(map(str, sorted(FULL))))
    if PARTIAL:
        print("partial IDs:")
        for source_id in sorted(PARTIAL):
            print(f"  {source_id}: {PARTIAL[source_id][1]}")
    print("unmapped IDs:", ", ".join(map(str, sorted(unmapped))))

    if args.strict and (set(FULL) != theorem_ids or PARTIAL):
        print("strict audit failed: not every theorem-like source environment is fully formalised", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
