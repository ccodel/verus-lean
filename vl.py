#
# The script coordinating the Verus-Lean pipeline.
# 
# Usage: python vl.py <path/to/verus/file.rs> <path/to/lean/File.lean>
#

import os
import sys
import subprocess
import argparse
import pathlib

################################################################################
# File management
################################################################################

def is_executable(path):
    return os.path.isfile(path) and os.access(path, os.X_OK)

# {F,R,W,X}_OK for existence, read, write, and execute permissions
def check_for_valid_file(path, rwe_opt):
    if not os.path.isfile(path):
        print("Error: The provided file does not exist:", path, file=sys.stderr)
        sys.exit(1)
    else:
        if not os.access(path, rwe_opt):
            if rwe_opt == os.F_OK:
                print("Error: The provided file either does not exist:", path, file=sys.stderr)
            elif rwe_opt == os.R_OK:
                print("Error: The provided file is not readable:", path, file=sys.stderr)
            elif rwe_opt == os.W_OK:
                print("Error: The provided file is not writeable:", path, file=sys.stderr)
            else:
                print("Error: The provided file is not executable:", path, file=sys.stderr)
            sys.exit(1)


def check_writeable_if_exists(path):
    if os.path.exists(path):
        if not os.access(path, os.W_OK):
            print("Error: The provided file exists but is not writeable:", path, file=sys.stderr)
            sys.exit(1)


def get_path_from_extensions(exts):
    # First, check if executable is in (some extension of) the $PATH
    exts.insert(0, '')
    for p in os.environ['PATH'].split(os.pathsep):
        for ext in exts:
            path = os.path.join(p, ext)
            if is_executable(path):
                return path

    # Now check if it exists in the current directory
    exts.pop(0)
    cwd = os.getcwd()
    for ext in exts:
        path = os.path.join(cwd, ext)
        if is_executable(path):
            return path
        
    return None


def get_verus_path():
    extensions = [
        'verus',
        'source/target-verus/release/verus',
        'verus/source/target-verus/release/verus',
    ]

    verus_path = get_path_from_extensions(extensions)
    if verus_path is None:
        print("Error: Cannot find `verus` in your $PATH.", file=sys.stderr)
        print("Add `verus` (or the directory containing it) to your $PATH.", file=sys.stderr)
        print("Alternatively, use the `--verus=<path>` option to specify a path for it.", file=sys.stderr)
        sys.exit(1)
    else:
        return verus_path
    

def get_verus_lean_path():
    extensions = [
        'verus-lean',
        'bin/verus-lean',
        '.lake/build/bin/verus-lean',
    ]

    verus_lean_path = get_path_from_extensions(extensions)
    if verus_lean_path is None:
        print("Error: Cannot find `verus-lean` binary in your $PATH.", file=sys.stderr)
        print("Add `verus-lean` (or the directory containing it) to your $PATH.", file=sys.stderr)
        print("Alternatively, use the `--verus-lean=<path>` option to specify a path for it.", file=sys.stderr)
        sys.exit(1)
    else:
        return verus_lean_path

# Scans until "MAGIC COMMENT END" is found. If `f` is not None, will print the lines
# Returns the index of the line after the magic comment
def scan_for_magic_comment(lines, idx, f):
    for i in range(idx, len(lines)):
        if f is not None:
            f.write(lines[i])
        if "MAGIC COMMENT END" in lines[i]:
            return i + 1
    print("Error: The Lean code does not contain the magic comment end.", file=sys.stderr)
    sys.exit(1)


def get_closing_brace(ch):
    if ch == "(":
        return ")"
    elif ch == "{":
        return "}"
    elif ch == "⦃":
        return "⦄"
    else:
        print("Error: The provided character is not a valid opening brace:", ch, file=sys.stderr)
        sys.exit(1)


# TODO: Make this not recursive
# TODO: Don't strip whitespace?
# Scans the lines until the matching closing brace is found
# Returns a pair of the line and char index of the char after the closing brace
def skip_to_closing_brace(lines, line_idx, char_idx, brace):
    for line_idx in range(line_idx, len(lines)):
        line = lines[line_idx].strip()
        for i in range(char_idx, len(line)):
            ch = line[i]
            if ch == brace:
                return (line_idx, i + 1)
            elif ch in "({⦃":
                (new_line_idx, new_char_idx) = skip_to_closing_brace(lines, line_idx, i + 1, get_closing_brace(ch))
                i = new_char_idx
                if line_idx != new_line_idx:
                    line_idx = new_line_idx
                    line = lines[line_idx].strip()
    
    print("Error: No matching closing brace found.", file=sys.stderr)
    sys.exit(1)

def skip_to_next_non_whitespace(lines, line_idx, char_idx):
    for line_idx in range(line_idx, len(lines)):
        line = lines[line_idx].strip()
        for i in range(char_idx, len(line)):
            ch = line[i]
            if ch != " ":
                return (line_idx, i)
        char_idx = 0
    
    print("Error: No non-whitespace character found.", file=sys.stderr)
    sys.exit(1)

# Returns the theorem statement until, but not including, the ending `:=`,
# ignoring new lines and double spaces (substituting them for a single space)
# Returns a pair of (name, statement, start_idx)
# TODO: Currently assuming that this section ends with `MAGIC COMMENT END`
# TODO: Assumes that the user does not use `:=` or braces in "evil" ways
def collect_theorem_statement(lines, line_idx):
    name = None
    statement = None
    start_idx = None

    # Find the start of the theorem
    for i in range(line_idx, len(lines)):
        # Assume that the theorem starts with `theorem`
        # TODO: @simp annotations?
        line = lines[i].strip()
        if line.startswith("theorem"):
            # TODO Assume that the theorem name immediately follows "theorem"
            name_start = 8   # 8 == len("theorem ")
            name_end = -1
            start_idx = i
            for j in range(name_start, len(line) + 1):
                if j == len(line) or line[j] == " ":
                    name_end = j
                    name = line[name_start:name_end]
                    break
            break

    # Skip ahead
    (line_idx, char_idx) = skip_to_next_non_whitespace(lines, i, name_end)

    # Now accumulate the theorem statement
    statement_start_line_idx = line_idx
    statement_start_char_idx = char_idx

    for i in range(line_idx, len(lines)):
        line = lines[i].strip()
        for j in range(char_idx, len(line)):
            char_idx = 0
            ch = line[j]
            if ch in "({⦃":
                (new_i, j) = skip_to_closing_brace(lines, i, j + 1, get_closing_brace(ch))
                if i != new_i:
                    line = lines[new_i].strip()
                    i = new_i
            elif j < len(line) - 1 and line[j] == ":" and line[j + 1] == "=":
                # We found the end of the theorem statement
                # Re-construct it
                statement = None
                if i == statement_start_line_idx:
                    statement = lines[i].strip()[statement_start_char_idx:(j - 1)].strip()
                else:
                    statement = lines[statement_start_line_idx].strip()[statement_start_char_idx:]
                    for k in range(statement_start_line_idx + 1, i):
                        statement += " " + lines[k].strip()
                    statement += " " + lines[i].strip()[:j - 1].strip()
                
                return (name, statement, start_idx)

    print("Error: No matching `:=` found for the theorem statement.", file=sys.stderr)
    sys.exit(1)

# Returns (line_idx, statements), where `line_idx` is one more than `MAGIC COMMENT END`
def collect_theorem_statements(lines, line_idx):
    statements = []
    while line_idx < len(lines) - 1 and "MAGIC COMMENT END" not in lines[line_idx + 1]:
        line = lines[line_idx].strip()
        if len(lines) == 0:
            continue
        elif line.startswith("theorem"):
            thm = collect_theorem_statement(lines, line_idx)
            statements.append(thm)
        line_idx += 1

    return (line_idx + 2, statements)

################################################################################
# Main execution
################################################################################

cwd = os.getcwd()

# Instantiate the CLI parser
parser = argparse.ArgumentParser(description='Script in charge of the Verus-Lean pipeline.')

parser.add_argument('--verus', type=pathlib.Path,
                    help='Path to `verus`. If not specified, the script will look for it in your $PATH.')
parser.add_argument('--verus-lean', type=pathlib.Path,
                    help='Path to `verus-lean`. If not specified, the script will look for it in your $PATH.')
header_group = parser.add_mutually_exclusive_group(required=False)
header_group.add_argument('--license', type=pathlib.Path,
                          help='Path to a license header file, which will be added to the top of the Lean file.')
header_group.add_argument('--header', type=pathlib.Path,
                            help='Path to a license header file, which will be added to the top of the Lean file.')

(parsed, remaining) = parser.parse_known_args(sys.argv[1:])

# Error if there are a wrong number of arguments
if len(remaining) != 2:
    # Print to stderr
    print("Error: Incorrect number of arguments", file=sys.stderr)
    print("Usage: python vl.py <path/to/verus/file.rs> <path/to/lean/File.lean>", file=sys.stderr)
    sys.exit(1)

# Store and check that the four needed files exists/have the right permissions
verus_file = remaining[0]
check_for_valid_file(verus_file, os.R_OK)

lean_file = remaining[1]
lean_file_exists = os.path.isfile(lean_file)
check_writeable_if_exists(lean_file)

verus_binary = parsed.verus
if verus_binary is None:
    verus_binary = get_verus_path()
else:
    check_for_valid_file(verus_binary, os.X_OK)

verus_lean_binary = parsed.verus_lean
if verus_lean_binary is None:
    verus_lean_binary = get_verus_lean_path()
else:
    check_for_valid_file(verus_lean_binary, os.X_OK)

print("Verus (.rs) file:", verus_file)
print("Lean (.lean) file:", lean_file)
print("verus:", verus_binary)
print("verus-lean:", verus_lean_binary)
print()

# 1. Run `verus` to generate a `serialized_{}` file in our current directory
#    Skip the rest of the pipeline if the hash is the same
verus_base_name = os.path.basename(verus_file).split(".")[0]
serialized_file = os.path.join(cwd, f"serialized_{verus_base_name}.json")
serialization_existed = os.path.exists(serialized_file) and os.access(serialized_file, os.R_OK)

# (Re-)generate the serialization
verus_result = subprocess.run([verus_binary, verus_file], capture_output=True, text=True)
if verus_result.returncode != 0:
    print("Error: verus failed to run successfully. Below is its error output:", file=sys.stderr)
    print(verus_result.stderr, file=sys.stderr)
    sys.exit(1)

# The serialized file should now be in our current directory
check_for_valid_file(serialized_file, os.R_OK)

# 2. Generate or update the Lean file
if not lean_file_exists:
    # If the Lean file doesn't exist, run `verus-lean` directly
    lean_result = subprocess.run([verus_lean_binary, serialized_file, lean_file], capture_output=True, text=True)
    if lean_result.returncode != 0:
        print("Error: verus-lean failed to run successfully. Below is its error output:", file=sys.stderr)
        print(lean_result.stderr, file=sys.stderr)
        sys.exit(1)
    else:
        print("Success! verus-lean generated the Lean file")
else:
    # The Lean file already exists - update the definitions
    check_for_valid_file(lean_file, os.R_OK)
    print("The Lean file already exists. Overwriting the definitions...")

    lines = []
    with open(lean_file, "r") as file:
        lines = file.readlines()

    # Pipe the new Lean generation to stdout
    # For now, assume that generation succeeded
    # TODO: As of 4/30, `Main.lean` catches all errors, so the return code will always be 0
    #       As a workaround, we check if the first line of output is an import statement
    lean_result = subprocess.run([verus_lean_binary, serialized_file], capture_output=True, text=True)
    if lean_result.returncode != 0 or not "import VerusLean.Basic" in lean_result.stdout:
        print("Error: verus-lean failed. Below is its error output:", file=sys.stderr)
        print(lean_result.stderr, file=sys.stderr)
        sys.exit(1)
    new_lines = lean_result.stdout.splitlines(keepends=True)

    # Erase previous contents
    f = open(lean_file, "w")

    # -> "Start section (1)"
    magic_index = scan_for_magic_comment(lines, 0, f)
    new_magic_index = scan_for_magic_comment(new_lines, 0, None)

    # -> "End section (1)"
    # Write new output over the old data structures section
    magic_index = scan_for_magic_comment(lines, magic_index, None)
    new_magic_index = scan_for_magic_comment(new_lines, new_magic_index, f)

    # -> "Start section (2)"
    # Write intervening code until user theorem statement section
    magic_index = scan_for_magic_comment(lines, magic_index, f)
    new_magic_index = scan_for_magic_comment(new_lines, new_magic_index, None)

    # -> "End section (2)"
    # Leave the old user theorem statements alone
    # TODO: Add missing/new theorem names

    (e, thms) = collect_theorem_statements(lines, magic_index)
    print("old theorem statements")
    for (name, statement, start_idx) in thms:
        print(f"theorem {name} {statement}")

    print("newly generated statements")
    (e_new, thms) = collect_theorem_statements(new_lines, new_magic_index)
    for (name, statement, start_idx) in thms:
        print(f"theorem {name} {statement}")

    magic_index = scan_for_magic_comment(lines, magic_index, f)
    new_magic_index = scan_for_magic_comment(new_lines, new_magic_index, None)

    # -> "Start section (3)"
    magic_index = scan_for_magic_comment(lines, magic_index, f)
    new_magic_index = scan_for_magic_comment(new_lines, new_magic_index, None)

    # -> "End section (3)"
    # Write the new user theorem statements
    magic_index = scan_for_magic_comment(lines, magic_index, None)
    new_magic_index = scan_for_magic_comment(new_lines, new_magic_index, f)

    # Write the rest of the old file
    for i in range(magic_index, len(lines)):
        f.write(lines[i])

    f.close()
    print("Success! Check the Lean file for the new definitions.")