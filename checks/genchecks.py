#!/usr/bin/env python3
#
# Copyright (C) 2017  Claire Xenia Wolf <claire@yosyshq.com>
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

import os, sys, shutil, re, shlex
from functools import reduce

nret = 1
isa = "rv32i"
ilen = 32
xlen = 32
buslen = 32
nbus = 1
csrs = set()
custom_csrs = set()
illegal_csrs = set()
csr_tests = {}
csr_spec = None
compr = False

depths = list()
groups = [None]
blackbox = False

cfgname = "checks"
basedir = f"{os.getcwd()}/../.."
corename = os.getcwd().split("/")[-1]
solver = "ric3"
config = dict()
mode = "prove"

if len(sys.argv) > 1:
    assert len(sys.argv) == 2
    cfgname = sys.argv[1]

print(f"Reading {cfgname}.cfg.")
with open(f"{cfgname}.cfg", "r") as f:
    cfgsection = None
    cfgsubsection = None
    for line in f:
        line = line.strip()

        if line.startswith("#"):
            continue

        if line.startswith("[") and line.endswith("]"):
            cfgsection = line.lstrip("[").rstrip("]")
            cfgsubsection = None
            if cfgsection.startswith("assume ") or cfgsection == "assume":
                cfgsubsection = cfgsection.split()[1:]
                cfgsection = "assume"
            continue

        if cfgsection is not None:
            if cfgsubsection is None:
                if cfgsection not in config:
                    config[cfgsection] = ""
                config[cfgsection] += f"{line}\n"
            else:
                if cfgsection not in config:
                    config[cfgsection] = []
                config[cfgsection].append((cfgsubsection, line))

if "options" in config:
    for line in config["options"].split("\n"):
        line = line.split()

        if len(line) == 0:
            continue

        elif line[0] == "nret":
            assert len(line) == 2
            nret = int(line[1])

        elif line[0] == "isa":
            assert len(line) == 2
            isa = line[1]

        elif line[0] == "blackbox":
            assert len(line) == 1
            blackbox = True

        elif line[0] == "solver":
            assert len(line) == 2
            if line[1] != "ric3":
                raise ValueError(
                    f"Unsupported solver '{line[1]}': only 'ric3' is allowed."
                )
            solver = line[1]

        elif line[0] == "dumpsmt2":
            assert len(line) == 1

        elif line[0] == "abspath":
            assert len(line) == 1

        elif line[0] == "mode":
            assert len(line) == 2
            if line[1] != "prove":
                raise ValueError(
                    f"Unsupported mode '{line[1]}': only 'prove' is allowed."
                )
            mode = line[1]

        elif line[0] == "buslen":
            assert len(line) == 2
            buslen = int(line[1])

        elif line[0] == "nbus":
            assert len(line) == 2
            nbus = int(line[1])

        elif line[0] == "csr_spec":
            assert len(line) == 2
            csr_spec = line[1]

        else:
            print(line)
            assert 0

# parse isa string
isa_regex = re.compile(
    r"^rv(?P<width>\d+)(?P<base>[ie])(?P<ext>[a-v]*)(?P<multi>_?[SZX]\w+)?$", re.I
)
try:
    isa_dict = isa_regex.match(isa).groupdict()
except AttributeError:
    print(f"Unable to parse isa string '{isa}'")
    exit(1)

isa_mods: list[str] = [isa_dict["base"].lower(), isa_dict["width"]]
for mod in isa_dict["ext"] or "":
    isa_mods.append(mod.lower())
for mod in (isa_dict["multi"] or "").split("_"):
    if mod:
        isa_mods.append(mod.title())

if isa_dict["width"] == "64":
    xlen = 64

if "c" in isa_mods:
    compr = True


def add_csr_tests(name, test_str):
    # use regex to split by spaces, unless those spaces are inside quotation marks
    # e.g. const="32'h dead_beef" is one match not two
    #      const="32'h 0"_mask="32'h dead_beef" is also one match
    tests = re.findall(r"((?:\S*?\"[^\"]*\")+|\S+)", test_str)
    csr_tests[name] = tests


def add_csr(csr_str):
    try:
        name, tests = csr_str.split(maxsplit=1)
        add_csr_tests(name, tests)
    except ValueError:  # no tests
        name = csr_str.strip()
    csrs.add(name)
    return name


def mask_bits(test: str, bits: "list[int]", mask_len: int, invert=False):
    mask = reduce(lambda x, y: x | 1 << y, bits, 0)
    fstring = f"{test}_mask={'~' if invert else ''}{mask_len}'b{{:0{mask_len}b}}"
    return fstring.format(mask)


if csr_spec == "1.12":
    spec_csrs = {
        "mvendorid": ["const"],
        "marchid": ["const"],
        "mimpid": ["const"],
        "mhartid": ["const"],
        "mconfigptr": ["const"],
        # All reserved bits should be 0
        "mstatus": [
            mask_bits(
                "zero",
                [0, 2, 4, *range(23, 31)]
                + ([31, *range(38, 63)] if xlen == 64 else []),
                xlen,
            )
        ],
        "misa": [
            mask_bits(
                "zero", [6, 10, 11, 14, 17, 19, 22, 24, 25, *range(26, xlen - 2)], xlen
            )
        ],
        "mie": None,
        "mtvec": None,
        "mscratch": ["any"],
        "mepc": None,
        "mcause": None,
        "mtval": None,
        "mip": None,
        "mcycle": ["inc"],
        "minstret": ["inc"],
    }
    spec_csrs.update({f"mhpmcounter{i}": None for i in range(3, 32)})
    spec_csrs.update({f"mhpmevent{i}": None for i in range(3, 32)})

    restricted_csrs = {
        "medeleg": ("s", "302", None),
        "mideleg": ("s", "303", None),
        "mcounteren": ("u", "306", None),
        "mstatush": ("32", "310", [mask_bits("zero", [4, 5], xlen, invert=True)]),
        "mtinst": ("h", "34A", None),
        "mtval2": ("h", "34B", None),
        "menvcfg": ("u", "30A", None),
        "menvcfgh": ("u", "31A", None),  # u-mode only *and* 32bit only
    }
    for name, data in restricted_csrs.items():
        if data[0] in isa_mods:
            spec_csrs[name] = data[2]
        else:
            illegal_csrs.add(
                (data[1], "m", "rw"),
            )

    for name, tests in spec_csrs.items():
        csrs.add(name)
        if tests:
            csr_tests[name] = tests

if "csrs" in config:
    for line in config["csrs"].split("\n"):
        if line:
            add_csr(line)

if "custom_csrs" in config:
    for line in config["custom_csrs"].split("\n"):
        try:
            addr, levels, csr_str = line.split(maxsplit=2)
        except ValueError:  # no csr
            continue
        name = add_csr(csr_str)
        custom_csrs.add((name, int(addr, base=16), levels))

if "illegal_csrs" in config:
    for line in config["illegal_csrs"].split("\n"):
        line = tuple(line.split())

        if len(line) == 0:
            continue

        assert len(line) == 3
        illegal_csrs.add(line)

if "groups" in config:
    groups += config["groups"].split()

print(f"Creating {cfgname} directory.")
shutil.rmtree(cfgname, ignore_errors=True)
os.mkdir(cfgname)

ric3_warnings = set()


def toml_quote(text):
    return '"' + text.replace("\\", "\\\\").replace('"', '\\"') + '"'


def print_toml_array(f, name, values):
    print(f"{name} = [", file=f)
    for value in values:
        print(f"  {toml_quote(value)},", file=f)
    print("]", file=f)


def unique_paths(paths):
    seen = set()
    ret = []
    for path in paths:
        key = os.path.normpath(path)
        if key not in seen:
            seen.add(key)
            ret.append(key)
    return ret


def parse_script_source_files(script_lines, check, section_name):
    source_files = []
    include_dirs = []
    for line in script_lines:
        try:
            words = shlex.split(line)
        except ValueError:
            continue
        if not words:
            continue
        if words[0] == "read":
            read_files = [word for word in words[1:] if not word.startswith("-")]
            source_files += read_files
        elif words[0] == "read_verilog":
            read_files = [word for word in words[1:] if not word.startswith("-")]
            source_files += read_files
        elif words[0] == "read_slang":
            read_files = [word for word in words[1:] if not word.startswith("-")]
            source_files += read_files
        elif words[0] == "read_vhdl":
            read_files = [word for word in words[1:] if not word.startswith("-")]
            source_files += read_files
        elif words[0] == "verilog_defaults":
            idx = 1
            while idx < len(words):
                word = words[idx]
                if word == "-I":
                    idx += 1
                    if idx < len(words):
                        include_dirs.append(words[idx])
                elif word.startswith("-I"):
                    include_dirs.append(word[2:])
                elif word in ("-add", "-clear"):
                    pass
                else:
                    ric3_warnings.add(
                        f"{check}: {section_name} command '{line}' uses unsupported verilog_defaults option '{word}'."
                    )
                idx += 1
        else:
            ric3_warnings.add(
                f"{check}: {section_name} command '{line}' cannot be represented in ric3.toml."
            )
    return unique_paths(source_files), unique_paths(include_dirs)


def write_generated_file(dst_path, lines):
    with open(dst_path, "w") as f:
        print("// Auto-generated by riscv-formal/checks/genchecks.py", file=f)
        for line in lines:
            print(line, file=f)


def write_generated_files(check, generated):
    project_dir = f"{cfgname}/{check}"
    os.makedirs(project_dir, exist_ok=True)
    generated_files = []
    for filename, lines in generated.items():
        write_generated_file(f"{project_dir}/{filename}", lines)
        generated_files.append((filename, os.path.join(project_dir, filename)))
    return generated_files


def discover_include_files(files, include_dirs, generated_basenames, check):
    include_re = re.compile(r'^\s*`include\s+"([^"]+)"')
    pending = [os.path.normpath(path) for path in files]
    scanned = set()
    found = []
    known_by_basename = {}

    for path in pending:
        name = os.path.basename(path)
        if name not in known_by_basename:
            known_by_basename[name] = path

    while pending:
        path = pending.pop()
        if path in scanned:
            continue
        scanned.add(path)

        try:
            with open(path, "r") as f:
                lines = list(f)
        except OSError:
            continue

        for line in lines:
            match = include_re.match(line)
            if not match:
                continue

            include_name = match.group(1)
            if os.path.basename(include_name) in generated_basenames:
                continue
            if os.path.basename(include_name) in ("assume_stmts.vh", "cover_stmts.vh"):
                continue

            if os.path.dirname(include_name):
                ric3_warnings.add(
                    f"{check}: include '{include_name}' uses a directory component. "
                    "rIC3 currently copies include_files into a flat src directory, so "
                    "this may need include-directory or path-preserving include support."
                )

            candidates = []
            known_path = known_by_basename.get(os.path.basename(include_name))
            if known_path is not None:
                candidates.append(known_path)
            if os.path.isabs(include_name):
                candidates.append(include_name)
            else:
                candidates.append(os.path.join(os.path.dirname(path), include_name))
                candidates.extend(
                    os.path.join(incdir, include_name) for incdir in include_dirs
                )

            resolved = None
            for candidate in candidates:
                candidate = os.path.normpath(candidate)
                if os.path.exists(candidate):
                    resolved = candidate
                    break

            if resolved is None:
                ric3_warnings.add(
                    f"{check}: ric3.toml could not resolve include '{include_name}' "
                    f"from {path}; rIC3 may need include-directory support."
                )
                continue

            if resolved not in found:
                found.append(resolved)
                pending.append(resolved)

    return found


def warn_duplicate_basenames(check, paths):
    seen = dict()
    for path in paths:
        name = os.path.basename(path)
        if name in seen and os.path.normpath(path) != os.path.normpath(seen[name]):
            ric3_warnings.add(
                f"{check}: ric3.toml cannot represent duplicate source basename '{name}' "
                f"({seen[name]} and {path}) because rIC3 copies sources into a flat src directory."
            )
        else:
            seen[name] = path


def collect_source_files(check, script_define_sections=()):
    script_sources = []
    include_dirs = []

    for section in script_define_sections:
        source_files, section_include_dirs = parse_script_source_files(
            hfmt(section, **hargs), check, "script-defines"
        )
        script_sources += source_files
        include_dirs += section_include_dirs

    if "verilog-files" in config:
        script_sources += hfmt(config["verilog-files"], **hargs)

    if "vhdl-files" in config:
        source_files = hfmt(config["vhdl-files"], **hargs)
        script_sources += source_files
        if source_files:
            ric3_warnings.add(
                f"{check}: vhdl-files are passed to ric3.toml as normal dut files; "
                "verify that rIC3/Yosys handles this input as expected."
            )

    if "script-sources" in config:
        source_files, section_include_dirs = parse_script_source_files(
            hfmt(config["script-sources"], **hargs), check, "script-sources"
        )
        script_sources += source_files
        include_dirs += section_include_dirs

    if "script-link" in config:
        ric3_warnings.add(
            f"{check}: script-link is ignored because ric3.toml does not expose an equivalent post-prep hook."
        )

    return unique_paths([f"{check}.sv"] + script_sources), unique_paths(include_dirs)


def write_ric3_project(check, source_files, include_files, include_dirs, generated):
    generated_files = write_generated_files(check, generated)
    generated_names = [name for (name, _) in generated_files]
    generated_paths = [path for (_, path) in generated_files]
    generated_basenames = {os.path.basename(name) for name in generated_names}

    files = unique_paths(source_files)

    include_files = unique_paths(
        include_files + [name for (name, _) in generated_files if name not in files]
    )
    include_files += discover_include_files(
        [
            os.path.join(cfgname, check, path) if not os.path.isabs(path) else path
            for path in files + include_files
        ]
        + generated_paths,
        include_dirs,
        generated_basenames,
        check,
    )
    include_files = unique_paths(include_files)

    warn_duplicate_basenames(check, files + include_files)

    project_dir = f"{cfgname}/{check}"
    with open(f"{project_dir}/ric3.toml", "w") as f:
        print("# Auto-generated by riscv-formal/checks/genchecks.py", file=f)
        print("[dut]", file=f)
        print('top = "rvfi_testbench"', file=f)
        print_toml_array(f, "files", files)
        if include_files:
            print_toml_array(f, "include_files", include_files)
        print('reset = "reset"', file=f)
        print("", file=f)
        print("[formal]", file=f)
        print('invariants = "invariants.sv"', file=f)


def hfmt(text, **kwargs):
    lines = []
    for line in text.split("\n"):
        match = re.match(r"^\s*: ?(.*)", line)
        if match:
            line = match.group(1)
        elif line.strip() == "":
            continue
        lines.append(
            re.sub(
                r"@([a-zA-Z0-9_]+)@", lambda match: str(kwargs[match.group(1)]), line
            )
        )
    return lines


hargs = dict()
hargs["basedir"] = basedir
hargs["core"] = corename
hargs["nret"] = nret
hargs["xlen"] = xlen
hargs["ilen"] = ilen
hargs["buslen"] = buslen
hargs["nbus"] = nbus
hargs["mode"] = mode
hargs["ilang_file"] = f"{corename}-hier.il"

if "cover" in config:
    hargs["cover"] = config["cover"]

instruction_checks = set()
consistency_checks = set()


def test_disabled(check):
    if "filter-checks" in config:
        for line in config["filter-checks"].split("\n"):
            line = line.strip().split()
            if len(line) == 0:
                continue
            assert len(line) == 2 and line[0] in ["-", "+"]
            if re.match(line[1], check):
                return line[0] == "-"
    return False


def get_depth_cfg(patterns):
    ret = None
    if "depth" in config:
        for line in config["depth"].split("\n"):
            line = line.strip().split()
            if len(line) == 0:
                continue
            for pat in patterns:
                if re.fullmatch(line[0], pat):
                    ret = [int(s) for s in line[1:]]
    return ret


def custom_csr_lines():
    lines = []
    fstrings = {
        "inputs": "  ,input [`RISCV_FORMAL_NRET * `RISCV_FORMAL_XLEN - 1 : 0] rvfi_csr_{csr}_{signal} \\",
        "wires": "  (* keep *) wire [`RISCV_FORMAL_NRET * `RISCV_FORMAL_XLEN - 1 : 0] rvfi_csr_{csr}_{signal}; \\",
        "conn": "  ,.rvfi_csr_{csr}_{signal} (rvfi_csr_{csr}_{signal}) \\",
        "channel": "  wire [`RISCV_FORMAL_XLEN - 1 : 0] csr_{csr}_{signal} = rvfi_csr_{csr}_{signal} [(_idx)*(`RISCV_FORMAL_XLEN) +: `RISCV_FORMAL_XLEN]; \\",
        "signals": "`RISCV_FORMAL_CHANNEL_SIGNAL(`RISCV_FORMAL_NRET, `RISCV_FORMAL_XLEN, csr_{csr}_{signal}) \\",
        "outputs": "  ,output [`RISCV_FORMAL_NRET * `RISCV_FORMAL_XLEN - 1 : 0] rvfi_csr_{csr}_{signal} \\",
        "indices": "  localparam [11:0] csr_{level}index_{name} = 12'h{index:03X}; \\",
    }
    for macro, fstring in fstrings.items():
        if macro == "channel":
            lines.append(f"`define RISCV_FORMAL_CUSTOM_CSR_{macro.upper()}(_idx) \\")
        else:
            lines.append(f"`define RISCV_FORMAL_CUSTOM_CSR_{macro.upper()} \\")
        for custom_csr in custom_csrs:
            name = custom_csr[0]
            addr = custom_csr[1]
            levels = custom_csr[2]
            if macro == "indices":
                for level in ["m", "s", "u"]:
                    if level in levels:
                        macro_string = fstring.format(
                            level=level, name=name, index=addr
                        )
                    else:
                        macro_string = fstring.format(
                            level=level, name=name, index=0xFFF
                        )
                    lines.append(macro_string)
            else:
                for signal in ["rmask", "wmask", "rdata", "wdata"]:
                    macro_string = fstring.format(csr=name, signal=signal)
                    lines.append(macro_string)
        lines.append("")
    return lines


def assume_lines_for_check(check):
    lines = []
    if "assume" not in config:
        return lines

    for pat, line in config["assume"]:
        enabled = True
        for p in pat:
            if p.startswith("!"):
                p = p[1:]
                enabled = False
            else:
                enabled = True
            if re.match(p, check):
                enabled = not enabled
                break
        if enabled:
            lines.append(line)
    return lines


# ------------------------------ Instruction Checkers ------------------------------


def check_insn(grp, insn, chanidx, csr_mode=False, illegal_csr=False):
    pf = "" if grp is None else grp + "_"
    if illegal_csr:
        ill_addr, ill_modes, ill_rw = insn
        insn = f"12'h{int(ill_addr, base=16):03X}"
        check = f"{pf}csr_ill_{ill_addr}_ch{chanidx:d}"
        depth_cfg = get_depth_cfg(
            [
                f"{pf}csr_ill",
                f"{pf}csr_ill_ch{chanidx:d}",
                f"{pf}csr_ill_{ill_addr}",
                f"{pf}csr_ill_{ill_addr}_ch{chanidx:d}",
            ]
        )
    else:
        if csr_mode:
            check = "csrw"
        else:
            check = "insn"
        depth_cfg = get_depth_cfg(
            [
                f"{pf}{check}",
                f"{pf}{check}_ch{chanidx:d}",
                f"{pf}{check}_{insn}",
                f"{pf}{check}_{insn}_ch{chanidx:d}",
            ]
        )
        check = f"{pf}{check}_{insn}_ch{chanidx:d}"

    if depth_cfg is None:
        return
    assert len(depth_cfg) == 1

    if test_disabled(check):
        return
    instruction_checks.add(check)

    hargs["insn"] = insn
    hargs["checkch"] = check
    hargs["channel"] = f"{chanidx:d}"
    hargs["depth"] = depth_cfg[0]
    hargs["depth_plus"] = depth_cfg[0] + 1
    hargs["skip"] = depth_cfg[0]

    script_define_sections = []
    if "script-defines" in config:
        script_define_sections.append(config["script-defines"])
    source_files, include_dirs = collect_source_files(check, script_define_sections)

    include_files = hfmt(
        """
            : @basedir@/checks/rvfi_macros.vh
            : @basedir@/checks/rvfi_channel.sv
            : @basedir@/checks/rvfi_testbench.sv
    """,
        **hargs,
    )

    if illegal_csr:
        include_files += hfmt(
            """
                : @basedir@/checks/rvfi_csr_ill_check.sv
        """,
            **hargs,
        )
    elif csr_mode:
        include_files += hfmt(
            """
                : @basedir@/checks/rvfi_csrw_check.sv
        """,
            **hargs,
        )
    else:
        include_files += hfmt(
            """
                : @basedir@/checks/rvfi_insn_check.sv
                : @basedir@/insns/insn_@insn@.v
        """,
            **hargs,
        )

    defines_lines = hfmt(
        """
            : `define RISCV_FORMAL
            : `define RISCV_FORMAL_NRET @nret@
            : `define RISCV_FORMAL_XLEN @xlen@
            : `define RISCV_FORMAL_ILEN @ilen@
            : `define RISCV_FORMAL_CHECK_CYCLE @depth@
            : `define RISCV_FORMAL_CHANNEL_IDX @channel@
    """,
        **hargs,
    )

    if "assume" in config:
        defines_lines.append("`define RISCV_FORMAL_ASSUME")

    if mode == "prove":
        defines_lines.append("`define RISCV_FORMAL_UNBOUNDED")

    for csr in sorted(csrs):
        defines_lines.append(f"`define RISCV_FORMAL_CSR_{csr.upper()}")

    if csr_mode and insn in ("mcycle", "minstret"):
        defines_lines.append("`define RISCV_FORMAL_CSRWH")

    if illegal_csr:
        defines_lines += hfmt(
            """
                : `define RISCV_FORMAL_CHECKER rvfi_csr_ill_check
                : `define RISCV_FORMAL_ILL_CSR_ADDR @insn@
        """,
            **hargs,
        )
        if "m" in ill_modes:
            defines_lines.append("`define RISCV_FORMAL_ILL_MMODE")
        if "s" in ill_modes:
            defines_lines.append("`define RISCV_FORMAL_ILL_SMODE")
        if "u" in ill_modes:
            defines_lines.append("`define RISCV_FORMAL_ILL_UMODE")
        if "r" in ill_rw:
            defines_lines.append("`define RISCV_FORMAL_ILL_READ")
        if "w" in ill_rw:
            defines_lines.append("`define RISCV_FORMAL_ILL_WRITE")
    elif csr_mode:
        defines_lines += hfmt(
            """
                : `define RISCV_FORMAL_CHECKER rvfi_csrw_check
                : `define RISCV_FORMAL_CSRW_NAME @insn@
        """,
            **hargs,
        )
    else:
        defines_lines += hfmt(
            """
                : `define RISCV_FORMAL_CHECKER rvfi_insn_check
                : `define RISCV_FORMAL_INSN_MODEL rvfi_insn_@insn@
        """,
            **hargs,
        )

    if custom_csrs:
        defines_lines += custom_csr_lines()

    if blackbox:
        defines_lines.append("`define RISCV_FORMAL_BLACKBOX_REGS")

    if compr:
        defines_lines.append("`define RISCV_FORMAL_COMPRESSED")

    if "defines" in config:
        defines_lines += hfmt(config["defines"], **hargs)

    defines_lines += hfmt(
        """
            : `include "rvfi_macros.vh"
    """,
        **hargs,
    )

    top_lines = hfmt(
        """
            : `include "defines.sv"
            : `include "rvfi_channel.sv"
            : `include "rvfi_testbench.sv"
    """,
        **hargs,
    )

    if illegal_csr:
        top_lines += hfmt(
            """
                : `include "rvfi_csr_ill_check.sv"
        """,
            **hargs,
        )
    elif csr_mode:
        top_lines += hfmt(
            """
                : `include "rvfi_csrw_check.sv"
        """,
            **hargs,
        )
    else:
        top_lines += hfmt(
            """
                : `include "rvfi_insn_check.sv"
                : `include "insn_@insn@.v"
        """,
            **hargs,
        )

    generated = {
        "defines.sv": defines_lines,
        f"{check}.sv": top_lines,
    }

    if "assume" in config:
        generated["assume_stmts.vh"] = assume_lines_for_check(check)

    write_ric3_project(check, source_files, include_files, include_dirs, generated)


for grp in groups:
    try:
        with open(f"../../insns/isa_{isa}.txt", "r") as isa_file:
            for insn in isa_file:
                for chanidx in range(nret):
                    check_insn(grp, insn.strip(), chanidx)
    except FileNotFoundError:
        print(
            f"Current isa string '{isa}' not supported, skipping instruction checks.",
            file=sys.stderr,
        )

    for csr in sorted(csrs):
        for chanidx in range(nret):
            check_insn(grp, csr, chanidx, csr_mode=True)

    for ill_csr in sorted(illegal_csrs, key=lambda csr: csr[0]):
        for chanidx in range(nret):
            check_insn(grp, ill_csr, chanidx, illegal_csr=True)

# ------------------------------ Consistency Checkers ------------------------------


def check_cons(
    grp,
    check,
    chanidx=None,
    start=None,
    trig=None,
    depth=None,
    csr_mode=False,
    csr_test=None,
    bus_mode=False,
):
    pf = "" if grp is None else grp + "_"
    if csr_mode:
        csr_name = check
        if csr_test is not None:
            # Check for provided mask
            mask_idx = csr_test.find("_mask")
            if mask_idx >= 0:
                try:
                    csr_mask = (
                        str(csr_test[mask_idx:]).split("=", maxsplit=1)[1].strip('"')
                    )
                except IndexError:  # no value provided
                    print(csr_test)
                    assert 0
                csr_test = csr_test[:mask_idx]
            if csr_test.startswith("const"):
                try:
                    constval = str(csr_test).split("=", maxsplit=1)[1].strip('"')
                except IndexError:  # no value provided
                    constval = "rdata_shadow"
                check = f"{pf}csrc_const_{csr_name}"
                check_name = f"csrc_const"
            elif csr_test.startswith("hpm"):
                try:
                    hpmevent = str(csr_test).split("=", maxsplit=1)[1].strip('"')
                except IndexError:  # no value provided
                    pass
                hpmcounter = str(csr_name).replace("event", "counter")
                if hpmcounter not in csrs:
                    csrs.add(hpmcounter)
                check = f"{pf}csrc_hpm_{csr_name}"
                check_name = f"csrc_hpm"
            else:
                check = f"{pf}csrc_{csr_test}_{csr_name}"
                check_name = f"csrc_{csr_test}"

        else:
            check = f"{pf}csrc_{csr_name}"
            check_name = "csrc"

        hargs["check"] = check_name

        if chanidx is not None:
            depth_cfg = get_depth_cfg(
                [
                    f"{pf}{check_name}",
                    check,
                    f"{pf}{check_name}_ch{chanidx:d}",
                    f"{check}_ch{chanidx:d}",
                ]
            )
            hargs["channel"] = f"{chanidx:d}"
            check = f"{check}_ch{chanidx:d}"

        else:
            depth_cfg = get_depth_cfg([f"{check_name}", check])
    else:
        hargs["check"] = check
        check = pf + check

        if chanidx is not None:
            depth_cfg = get_depth_cfg([check, f"{check}_ch{chanidx:d}"])
            hargs["channel"] = f"{chanidx:d}"
            check = f"{check}_ch{chanidx:d}"

        else:
            depth_cfg = get_depth_cfg([check])

    if depth_cfg is None:
        return

    if start is not None:
        start = depth_cfg[start]
    else:
        start = 1

    if start != 1:
        raise ValueError(
            f"{check}: rIC3 requires start to be 1, got configured start {start}."
        )

    if trig is not None:
        trig = depth_cfg[trig]

    if depth is not None:
        depth = depth_cfg[depth]

    hargs["start"] = start
    hargs["depth"] = depth
    hargs["depth_plus"] = depth + 1
    hargs["skip"] = depth

    hargs["checkch"] = check

    if test_disabled(check):
        return
    consistency_checks.add(check)
    script_define_sections = []
    if "script-defines" in config:
        script_define_sections.append(config["script-defines"])
    specific_script_defines = f"script-defines {hargs['check']}"
    if specific_script_defines in config:
        script_define_sections.append(config[specific_script_defines])

    source_files, include_dirs = collect_source_files(check, script_define_sections)

    include_files = hfmt(
        """
            : @basedir@/checks/rvfi_macros.vh
            : @basedir@/checks/rvfi_channel.sv
            : @basedir@/checks/rvfi_testbench.sv
            : @basedir@/checks/rvfi_@check@_check.sv
    """,
        **hargs,
    )

    defines_lines = hfmt(
        """
            : `define RISCV_FORMAL
            : `define RISCV_FORMAL_NRET @nret@
            : `define RISCV_FORMAL_XLEN @xlen@
            : `define RISCV_FORMAL_ILEN @ilen@
            : `define RISCV_FORMAL_CHECKER rvfi_@check@_check
            : `define RISCV_FORMAL_CHECK_CYCLE @depth@
    """,
        **hargs,
    )

    if "assume" in config:
        defines_lines.append("`define RISCV_FORMAL_ASSUME")

    if mode == "prove":
        defines_lines.append("`define RISCV_FORMAL_UNBOUNDED")

    for csr in sorted(csrs):
        defines_lines.append(f"`define RISCV_FORMAL_CSR_{csr.upper()}")

    if csr_mode:
        csr_defs = {
            "RISCV_FORMAL_CSRC_CONSTVAL": locals().get("constval"),
            "RISCV_FORMAL_CSRC_HPMEVENT": locals().get("hpmevent"),
            "RISCV_FORMAL_CSRC_HPMCOUNTER": locals().get("hpmcounter"),
            "RISCV_FORMAL_CSRC_MASK": locals().get("csr_mask"),
        }
        for key, value in csr_defs.items():
            if value is not None:
                defines_lines.append(f"`define {key} {value}")
        defines_lines.append(f"`define RISCV_FORMAL_CSRC_NAME {csr_name}")

    if custom_csrs:
        defines_lines += custom_csr_lines()

    if blackbox and hargs["check"] != "liveness":
        defines_lines.append("`define RISCV_FORMAL_BLACKBOX_ALU")

    if blackbox and hargs["check"] != "reg":
        defines_lines.append("`define RISCV_FORMAL_BLACKBOX_REGS")

    if chanidx is not None:
        defines_lines.append(f"`define RISCV_FORMAL_CHANNEL_IDX {chanidx:d}")

    if trig is not None:
        defines_lines.append(f"`define RISCV_FORMAL_TRIG_CYCLE {trig:d}")

    if bus_mode:
        defines_lines += hfmt(
            """
                : `define RISCV_FORMAL_BUS
                : `define RISCV_FORMAL_NBUS @nbus@
                : `define RISCV_FORMAL_BUSLEN @buslen@
        """,
            **hargs,
        )

    if hargs["check"] in ("liveness", "hang"):
        defines_lines.append("`define RISCV_FORMAL_FAIRNESS")

    if "defines" in config:
        defines_lines += hfmt(config["defines"], **hargs)

    specific_defines = f"defines {hargs['check']}"
    if specific_defines in config:
        defines_lines += hfmt(config[specific_defines], **hargs)

    defines_lines += hfmt(
        """
            : `include "rvfi_macros.vh"
    """,
        **hargs,
    )

    top_lines = hfmt(
        """
            : `include "defines.sv"
            : `include "rvfi_channel.sv"
            : `include "rvfi_testbench.sv"
            : `include "rvfi_@check@_check.sv"
    """,
        **hargs,
    )

    generated = {
        "defines.sv": defines_lines,
        f"{check}.sv": top_lines,
    }

    if hargs["check"] == "cover":
        generated["cover_stmts.vh"] = hfmt(config.get("cover", ""), **hargs)

    if "assume" in config:
        generated["assume_stmts.vh"] = assume_lines_for_check(check)

    write_ric3_project(check, source_files, include_files, include_dirs, generated)


for grp in groups:
    for i in range(nret):
        check_cons(grp, "reg", chanidx=i, start=0, depth=1)
        check_cons(grp, "pc_fwd", chanidx=i, start=0, depth=1)
        check_cons(grp, "pc_bwd", chanidx=i, start=0, depth=1)
        check_cons(grp, "liveness", chanidx=i, start=0, trig=1, depth=2)
        check_cons(grp, "unique", chanidx=i, start=0, trig=1, depth=2)
        check_cons(grp, "causal", chanidx=i, start=0, depth=1)
        check_cons(grp, "causal_mem", chanidx=i, start=0, depth=1)
        check_cons(grp, "causal_io", chanidx=i, start=0, depth=1)
        check_cons(grp, "ill", chanidx=i, depth=0)
        check_cons(grp, "fault", chanidx=i, depth=0)

        check_cons(grp, "bus_imem", chanidx=i, start=0, depth=1, bus_mode=True)
        check_cons(grp, "bus_imem_fault", chanidx=i, start=0, depth=1, bus_mode=True)
        check_cons(grp, "bus_dmem", chanidx=i, start=0, depth=1, bus_mode=True)
        check_cons(grp, "bus_dmem_fault", chanidx=i, start=0, depth=1, bus_mode=True)
        check_cons(grp, "bus_dmem_io_read", chanidx=i, start=0, depth=1, bus_mode=True)
        check_cons(
            grp, "bus_dmem_io_read_fault", chanidx=i, start=0, depth=1, bus_mode=True
        )
        check_cons(grp, "bus_dmem_io_write", chanidx=i, start=0, depth=1, bus_mode=True)
        check_cons(
            grp, "bus_dmem_io_write_fault", chanidx=i, start=0, depth=1, bus_mode=True
        )
        check_cons(grp, "bus_dmem_io_order", chanidx=i, start=0, depth=1, bus_mode=True)

    check_cons(grp, "hang", start=0, depth=1)
    check_cons(grp, "cover", start=0, depth=1)

    for csr in sorted(csrs):
        for chanidx in range(nret):
            for csr_test in csr_tests.get(csr, [None]):
                check_cons(
                    grp,
                    csr,
                    chanidx,
                    start=0,
                    depth=1,
                    csr_mode=True,
                    csr_test=csr_test,
                )

print(f"Generated {len(consistency_checks) + len(instruction_checks)} checks.")
print(
    f"Generated {len(consistency_checks) + len(instruction_checks)} rIC3 projects in {cfgname}."
)
if ric3_warnings:
    print("rIC3 generation warnings:", file=sys.stderr)
    for warning in sorted(ric3_warnings):
        print(f"  - {warning}", file=sys.stderr)
