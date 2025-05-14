# verus-lean: A Verus-Lean connection

The Lean backend to a [verus fork](https://github.com/ccodel/verus)
that allows for the export of verus definitions and verification conditions to Lean.

## Building

All building/compiling is done at the root level of the project,
unless otherwise indicated.

If you haven't set up the project yet, run
```
lake update          # Installs Lean and its dependencies
lake exe cache get   # Downloads pre-compiled .olean files
```

After, and for all subsequent builds, run
```
lake build
```

The compiled binary can be found at `.lake/build/bin/verus-lean`.

(I find it helpful to symlink the `bin/` folder at root level: `ln -s .lake/build/bin bin`,
or perhaps even better, `ln -s .lake/build/bin/verus-lean verus-lean`.)

## Running

You can run the compiled `verus-lean` binary directly:
```
./lake/build/bin/verus-lean <path/to/serialized_verus.json> [path/to/lean/output.lean]
```
Alternatively, you can use a Python script that works in concert with my verus fork.
(The script assumes that this fork is on your `$PATH`, or is (symlinked) at the root level of the project.)

To use this script, run
```
python vl.py <path/to/verus.rs> <path/to/lean/output.lean>
```

One benefit of the Python script is that it (semi-)intelligently updates the declarations if the source verus `.rs` file changes.
This replacement is very experimental, so be careful not to lose your work in Lean!


## Contributors

- Cayden Codel, PhD student at Carnegie Mellon University (ccodel@andrew.cmu.edu)
- James Gallicchio, PhD student at Carnegie Mellon University (jgallicc@andrew.cmu.edu)