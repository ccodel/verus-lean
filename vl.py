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


# Returns index of next declaration after (and not including) this one
def scan_for_next_declaration(lines, idx):
    for i in range(idx, len(lines)):
        line = lines[i].strip()
        if line.startswith("def") or line.startswith("theorem"):
            return i
    return -1


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
def collect_declaration(lines, line_idx):
    name = None
    statement = None
    start_idx = None

    # Find the start of the declaration
    i = scan_for_next_declaration(lines, line_idx)
    if i == -1:
        return None

    line = lines[i].strip()
    is_theorem = line.startswith("theorem")
    name_start = 8 if is_theorem else 4
    name_end = -1
    start_idx = i
    for j in range(name_start, len(line) + 1):
        if j == len(line) or line[j] == " ":
            name_end = j
            name = line[name_start:name_end]
            break

    # Skip ahead
    (line_idx, char_idx) = skip_to_next_non_whitespace(lines, i, name_end)

    # Now accumulate the declaration
    statement_start_line_idx = line_idx
    statement_start_char_idx = char_idx

    for i in range(line_idx, len(lines)):
        line = lines[i].strip()
        for j in range(char_idx, len(line)):
            ch = line[j]
            if ch in "({⦃":
                (new_i, j) = skip_to_closing_brace(lines, i, j + 1, get_closing_brace(ch))
                if i != new_i:
                    line = lines[new_i].strip()
                    i = new_i
            elif j < len(line) - 1 and line[j] == ":" and line[j + 1] == "=":
                # We found the end of the def/theorem statement
                # Re-construct it
                statement = None
                if i == statement_start_line_idx:
                    statement = lines[i].strip()[statement_start_char_idx:(j - 1)].strip()
                else:
                    statement = lines[statement_start_line_idx].strip()[statement_start_char_idx:]
                    for k in range(statement_start_line_idx + 1, i):
                        statement += " " + lines[k].strip()
                    statement += " " + lines[i].strip()[:j - 1].strip()
                
                return (name, statement, start_idx, i, j + 2)
        char_idx = 0

    print("Error: No matching `:=` found for the declaration.", file=sys.stderr)
    sys.exit(1)


# Returns (line_idx, statements), where `line_idx` is one more than `MAGIC COMMENT END`
def collect_declarations(lines, line_idx):
    statements = []
    prev_line_idx = -1
    while line_idx < len(lines) - 1:
        line = lines[line_idx].strip()
        if len(line) == 0:
            line_idx += 1
            continue
        elif line.startswith("theorem") or line.startswith("def"):
            decl = collect_declaration(lines, line_idx)
            if decl is not None:
                prev_line_idx = line_idx
                statements.append(decl)
            else:
                break
        line_idx += 1

    return (prev_line_idx + 1, statements)


def scan_backwards_for_whitespace(lines, line_idx, min_index):
    while line_idx > min_index and lines[line_idx].strip() != "":
        line_idx -= 1
    return line_idx

def write_new_theorem(lines, f, thms, i, mi, with_comment):
    start_idx = 0
    if with_comment:
        start_idx = 1 + scan_backwards_for_whitespace(lines, thms[i][2], mi)
    else:
        start_idx = thms[i][2]

    # TODO: Assumes that the declaration ends on a newline
    while start_idx < len(lines):
        f.write(lines[start_idx])
        line = lines[start_idx].strip()
        start_idx += 1
        if len(line) == 0:
            break


def copy_declarations(lines, new_lines, magic_index, new_magic_index, f):
    (old_end, old_thms) = collect_declarations(lines, magic_index)
    (new_end, new_thms) = collect_declarations(new_lines, new_magic_index)

    # Run through the old declarations line-by-line and update statements in place
    # After each match with a "new name," check if the next new declaration
    # is included in the old declarations.
    # If it is, we will process it in turn
    # If it isn't, then our best guess of where to put the new declaration is
    # immediately after the previous old one

    # 0. Collect theorem names and map to their indexes
    #    Assumes no duplicate names
    old_names = {}
    for i in range(len(old_thms)):
        name = old_thms[i][0]
        old_names[name] = i

    new_names = {}
    new_names_in_order = []
    for i in range(len(new_thms)):
        name = new_thms[i][0]
        new_names[name] = i
        new_names_in_order.append(name)

    # Space after prelude comment
    f.write("\n")

    # Write down any new declarations not preceded by old names
    for i in range(len(new_names_in_order)):
        name = new_names_in_order[i]
        if old_names.get(name) is None:
            write_new_theorem(new_lines, f, new_thms, i, new_magic_index, True)
        else:
            break

    # Now copy over the old declarations (with updated statements) line by line
    i = magic_index + 1
    while i < len(lines):
        line = lines[i].strip()
        # TODO: Assumes that we don't start with `@simp`
        if line.startswith("theorem") or line.startswith("def"):
            # Check if its name exists in the new names
            # TODO: Assumes the name is the second token
            #       (In reality, it could be on a new line [but this never happens])
            name = line.split()[1]
            old_idx = old_names[name]
            (_, old_statement, old_line_idx, old_st_end_line_idx, old_st_end_char_idx) = old_thms[old_idx]
            kind = "theorem" if line.startswith("theorem") else "def"
            if new_names.get(name) is not None:
                new_idx = new_names[name]
                (_, statement, line_idx, st_end_line_idx, st_end_char_idx) = new_thms[new_idx]

                # Always (and blindly) update definitions
                if kind == "def":
                    write_new_theorem(new_lines, f, new_thms, new_idx, new_magic_index, False)
                    # Assume that the definition stops with a newline
                    while i < len(lines):
                        line = lines[i].strip()
                        if line == "":
                            break
                        i += 1

                # Update (theorem) statement if it's different
                elif statement != old_statement:
                    # Write old statement body in a comment
                    f.write("/- NOTE: The declaration has changed. It used to be the following:\n")
                    f.write("   (You can safely delete this comment.)\n")
                    # TODO long statements have no line breaks
                    f.write(f"  theorem {name} {old_statement} := ...\n")
                    f.write("-/\n")

                    # Write new statement
                    for j in range(line_idx, st_end_line_idx):
                        f.write(new_lines[j])
                    f.write(new_lines[st_end_line_idx].strip()[:st_end_char_idx])

                    # Write old proof - start with the rest of the proof statement line
                    f.write(lines[old_st_end_line_idx].strip()[old_st_end_char_idx:])
                    f.write("\n")

                    end_idx = 0
                    if old_idx == len(old_thms) - 1:
                        end_idx = scan_backwards_for_whitespace(lines, old_end - 1, magic_index)
                    else:
                        end_idx = scan_backwards_for_whitespace(lines, old_thms[old_idx + 1][2], magic_index) 

                    # Copy over the rest of the old proof, written below the statement
                    for j in range(old_st_end_line_idx + 1, end_idx + 1):
                        f.write(lines[j])
                    i = end_idx + 1
                else:
                    f.write(lines[i])
                    pass

                # No matter what happens above:
                # Write down brand-new declarations if they follow a matching old one
                # TODO: Better heuristic is to put these after the max of the old names that came before
                #       But that's complicated
                for new_i in range(new_idx + 1, len(new_names_in_order)):
                    next_new_name = new_names_in_order[new_i]
                    if old_names.get(next_new_name) is None:
                        print(f"Missing declaration with the name {next_new_name}")
                        write_new_theorem(new_lines, f, new_thms, new_i, new_magic_index, True)
                    else:
                        break
            else: # new_names[name] is None
                f.write(lines[i])
        else:
            f.write(lines[i])
        i += 1


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

    # Re-open the Lean file, erasing previous contents
    f = open(lean_file, "w")

    # -> "end of prelude"
    magic_index = scan_for_magic_comment(lines, 0, f)
    new_magic_index = scan_for_magic_comment(new_lines, 0, None)

    copy_declarations(lines, new_lines, magic_index, new_magic_index, f)

    f.close()
    print("Success! Check the Lean file for the new definitions.")