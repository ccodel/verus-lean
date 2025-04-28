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
# TODO: Where to store hash?
verus_base_name = os.path.basename(verus_file).split(".")[0]
serialized_file = os.path.join(cwd, f"serialized_{verus_base_name}.json")

verus_result = subprocess.run([verus_binary, verus_file], capture_output=True, text=True)
if verus_result.returncode != 0:
    print("Error: verus failed to run successfully. Below is its error output:", file=sys.stderr)
    print(verus_result.stderr, file=sys.stderr)
    sys.exit(1)

# The serialized file should now be in our current directory
print("Success! verus serialized the file to:", serialized_file)
check_for_valid_file(serialized_file, os.R_OK)

# 2. Generate and write down a hash of the serialization
# TODO fast path if hash is the same
hash_result = subprocess.run(["sha256sum", serialized_file], capture_output=True, text=True)
hash_value = hash_result.stdout.split()[0]
hash_file_path = os.path.join(cwd, f"serialized_{verus_base_name}.sha256")
hash_file = open(hash_file_path, "w")
hash_file.write(hash_value + "\n")
hash_file.close()

# 3. Generate or update the Lean file
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
    # TODO HERE
    check_for_valid_file(lean_file, os.R_OK)
    print("The Lean file already exists. Overwriting the definitions...")

    lines = []
    with open(lean_file, "r") as file:
        lines = file.readlines()

    # Pipe the new Lean generation to stdout
    lean_result = subprocess.run([verus_lean_binary, serialized_file], capture_output=True, text=True)
    if lean_result.returncode != 0:
        print("Error: verus-lean failed to run successfully. Below is its error output:", file=sys.stderr)
        print(lean_result.stderr, file=sys.stderr)
        sys.exit(1)
    new_lines = lean_result.stdout.splitlines(keepends=True)

    # Erase previous contents
    f = open(lean_file, "w")

    # Scan forward for "MAGIC COMMENT END", writing previous contents line by line
    magic_index = -1
    for i in range(len(lines)):
        f.write(lines[i])
        if "MAGIC COMMENT END" in lines[i]:
            # The comment ends three lines after this one
            f.write(lines[i + 1])
            f.write(lines[i + 2])
            f.write(lines[i + 3])
            magic_index = i + 3
            break

    if magic_index == -1:
        print("Error: The Lean file does not contain the magic comment end.", file=sys.stderr)
        sys.exit(1)

    # TODO More intelligently replace things
    new_magic_index = -1
    for i in range(len(new_lines)):
        if "MAGIC COMMENT END" in new_lines[i]:
            new_magic_index = i + 3
            break

    # TODO just write the output until the second magic end
    for i in range(new_magic_index, len(new_lines)):
        f.write(new_lines[i])
        if "MAGIC COMMENT END" in new_lines[i]:
            # The comment ends three lines after this one
            f.write(new_lines[i + 1])
            f.write(new_lines[i + 2])
            f.write(new_lines[i + 3])
            break

    # Scan forward for the ending "MAGIC COMMENT END"
    for i in range(magic_index, len(lines)):
        if "MAGIC COMMENT END" in lines[i]:
            # The comment ends three lines after this one
            magic_index = i + 3
            break

    for i in range(magic_index, len(lines)):
        f.write(lines[i])

    f.close()
    print("Success! Check the Lean file for the new definitions.")