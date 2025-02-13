import Lean
import Lean.PrettyPrinter
import VerusLean

open VerusLean

open Lean PrettyPrinter

def ex1 : Json := json% {
  "Binary": [
    {
      "Eq": "Spec"
    },
    {
      "span": {
        "id": 79,
        "data": [
          12226565837067709479,
          1786706395564
        ],
        "as_string": "../by_lean.rs:18:10: 18:22 (#0)"
      },
      "typ": {
        "Int": {
          "U": 32
        }
      },
      "x": {
        "Binary": [
          {
            "Bitwise": [
              "BitAnd",
              "Spec"
            ]
          },
          {
            "span": {
              "id": 75,
              "data": [
                12226565837067709479,
                1786706395554
              ],
              "as_string": "../by_lean.rs:18:10: 18:12 (#0)"
            },
            "typ": {
              "Int": {
                "U": 32
              }
            },
            "x": {
              "Unary": [
                {
                  "BitNot": {
                    "Width": 32
                  }
                },
                {
                  "span": {
                    "id": 74,
                    "data": [
                      12226565837067709479,
                      1791001362850
                    ],
                    "as_string": "../by_lean.rs:18:11: 18:12 (#0)"
                  },
                  "typ": {
                    "Int": {
                      "U": 32
                    }
                  },
                  "x": {
                    "Var": [
                      "a",
                      "VirParam"
                    ]
                  }
                }
              ]
            }
          },
          {
            "span": {
              "id": 78,
              "data": [
                12226565837067709479,
                1808181232044
              ],
              "as_string": "../by_lean.rs:18:15: 18:22 (#0)"
            },
            "typ": {
              "Int": {
                "U": 32
              }
            },
            "x": {
              "Binary": [
                {
                  "Bitwise": [
                    "BitXor",
                    "Spec"
                  ]
                },
                {
                  "span": {
                    "id": 76,
                    "data": [
                      12226565837067709479,
                      1812476199335
                    ],
                    "as_string": "../by_lean.rs:18:16: 18:17 (#0)"
                  },
                  "typ": {
                    "Int": {
                      "U": 32
                    }
                  },
                  "x": {
                    "Var": [
                      "a",
                      "VirParam"
                    ]
                  }
                },
                {
                  "span": {
                    "id": 77,
                    "data": [
                      12226565837067709479,
                      1829656068523
                    ],
                    "as_string": "../by_lean.rs:18:20: 18:21 (#0)"
                  },
                  "typ": {
                    "Int": {
                      "U": 32
                    }
                  },
                  "x": {
                    "Var": [
                      "a",
                      "VirParam"
                    ]
                  }
                }
              ]
            }
          }
        ]
      }
    },
    {
      "span": {
        "id": 86,
        "data": [
          12226565837067709479,
          1855425872323
        ],
        "as_string": "../by_lean.rs:18:26: 18:45 (#0)"
      },
      "typ": {
        "Int": {
          "U": 32
        }
      },
      "x": {
        "Binary": [
          {
            "Bitwise": [
              "BitOr",
              "Spec"
            ]
          },
          {
            "span": {
              "id": 82,
              "data": [
                12226565837067709479,
                1855425872312
              ],
              "as_string": "../by_lean.rs:18:26: 18:34 (#0)"
            },
            "typ": {
              "Int": {
                "U": 32
              }
            },
            "x": {
              "Binary": [
                {
                  "Bitwise": [
                    {
                      "Shl": [
                        {
                          "Width": 32
                        },
                        false
                      ]
                    },
                    "Spec"
                  ]
                },
                {
                  "span": {
                    "id": 80,
                    "data": [
                      12226565837067709479,
                      1859720839602
                    ],
                    "as_string": "../by_lean.rs:18:27: 18:28 (#0)"
                  },
                  "typ": {
                    "Int": {
                      "U": 32
                    }
                  },
                  "x": {
                    "Var": [
                      "a",
                      "VirParam"
                    ]
                  }
                },
                {
                  "span": {
                    "id": 81,
                    "data": [
                      12226565837067709479,
                      1881195676087
                    ],
                    "as_string": "../by_lean.rs:18:32: 18:33 (#0)"
                  },
                  "typ": {
                    "Int": {
                      "I": 32
                    }
                  },
                  "x": {
                    "Const": {
                      "Int": [
                        1,
                        [
                          1
                        ]
                      ]
                    }
                  }
                }
              ]
            }
          },
          {
            "span": {
              "id": 85,
              "data": [
                12226565837067709479,
                1902670512579
              ],
              "as_string": "../by_lean.rs:18:37: 18:45 (#0)"
            },
            "typ": {
              "Int": {
                "U": 32
              }
            },
            "x": {
              "Binary": [
                {
                  "Bitwise": [
                    {
                      "Shr": {
                        "Width": 32
                      }
                    },
                    "Spec"
                  ]
                },
                {
                  "span": {
                    "id": 83,
                    "data": [
                      12226565837067709479,
                      1906965479869
                    ],
                    "as_string": "../by_lean.rs:18:38: 18:39 (#0)"
                  },
                  "typ": {
                    "Int": {
                      "U": 32
                    }
                  },
                  "x": {
                    "Var": [
                      "a",
                      "VirParam"
                    ]
                  }
                },
                {
                  "span": {
                    "id": 84,
                    "data": [
                      12226565837067709479,
                      1928440316354
                    ],
                    "as_string": "../by_lean.rs:18:43: 18:44 (#0)"
                  },
                  "typ": {
                    "Int": {
                      "I": 32
                    }
                  },
                  "x": {
                    "Const": {
                      "Int": [
                        1,
                        [
                          1
                        ]
                      ]
                    }
                  }
                }
              ]
            }
          }
        ]
      }
    }
  ]
}

def ex2 : Json := json% {
  "Binary": [
    {
      "Eq": "Spec"
    },
    {
      "span": {
        "id": 42,
        "data": [
          12226565837067709479,
          1047972020473
        ],
        "as_string": "../by_lean.rs:12:10: 12:15 (#0)"
      },
      "typ": {
        "Int": "Int"
      },
      "x": {
        "Binary": [
          {
            "Arith": [
              "Add",
              "Spec"
            ]
          },
          {
            "span": {
              "id": 40,
              "data": [
                12226565837067709479,
                1047972020469
              ],
              "as_string": "../by_lean.rs:12:10: 12:11 (#0)"
            },
            "typ": {
              "Int": "Int"
            },
            "x": {
              "Var": [
                "x",
                "VirParam"
              ]
            }
          },
          {
            "span": {
              "id": 41,
              "data": [
                12226565837067709479,
                1065151889657
              ],
              "as_string": "../by_lean.rs:12:14: 12:15 (#0)"
            },
            "typ": {
              "Int": "Int"
            },
            "x": {
              "Var": [
                "y",
                "VirParam"
              ]
            }
          }
        ]
      }
    },
    {
      "span": {
        "id": 45,
        "data": [
          12226565837067709479,
          1086626726146
        ],
        "as_string": "../by_lean.rs:12:19: 12:24 (#0)"
      },
      "typ": {
        "Int": "Int"
      },
      "x": {
        "Binary": [
          {
            "Arith": [
              "Add",
              "Spec"
            ]
          },
          {
            "span": {
              "id": 43,
              "data": [
                12226565837067709479,
                1086626726142
              ],
              "as_string": "../by_lean.rs:12:19: 12:20 (#0)"
            },
            "typ": {
              "Int": "Int"
            },
            "x": {
              "Var": [
                "y",
                "VirParam"
              ]
            }
          },
          {
            "span": {
              "id": 44,
              "data": [
                12226565837067709479,
                1103806595330
              ],
              "as_string": "../by_lean.rs:12:23: 12:24 (#0)"
            },
            "typ": {
              "Int": "Int"
            },
            "x": {
              "Var": [
                "x",
                "VirParam"
              ]
            }
          }
        ]
      }
    }
  ]
}

def ex3 : Json := json% {
  "Binary": [
    "Implies",
    {
      "span": {
        "id": 33,
        "data": [
          12226565837067709479,
          880468295891
        ],
        "as_string": "../by_lean.rs:11:10: 11:16 (#0)"
      },
      "typ": "Bool",
      "x": {
        "Binary": [
          {
            "Eq": "Spec"
          },
          {
            "span": {
              "id": 31,
              "data": [
                12226565837067709479,
                880468295886
              ],
              "as_string": "../by_lean.rs:11:10: 11:11 (#0)"
            },
            "typ": {
              "Int": "Int"
            },
            "x": {
              "Var": [
                "x",
                "VirParam"
              ]
            }
          },
          {
            "span": {
              "id": 32,
              "data": [
                12226565837067709479,
                901943132371
              ],
              "as_string": "../by_lean.rs:11:15: 11:16 (#0)"
            },
            "typ": {
              "Int": "Int"
            },
            "x": {
              "Var": [
                "y",
                "VirParam"
              ]
            }
          }
        ]
      }
    },
    {
      "span": {
        "id": 36,
        "data": [
          12226565837067709479,
          927712936158
        ],
        "as_string": "../by_lean.rs:11:21: 11:27 (#0)"
      },
      "typ": "Bool",
      "x": {
        "Binary": [
          {
            "Eq": "Spec"
          },
          {
            "span": {
              "id": 34,
              "data": [
                12226565837067709479,
                927712936153
              ],
              "as_string": "../by_lean.rs:11:21: 11:22 (#0)"
            },
            "typ": {
              "Int": "Int"
            },
            "x": {
              "Var": [
                "y",
                "VirParam"
              ]
            }
          },
          {
            "span": {
              "id": 35,
              "data": [
                12226565837067709479,
                949187772638
              ],
              "as_string": "../by_lean.rs:11:26: 11:27 (#0)"
            },
            "typ": {
              "Int": "Int"
            },
            "x": {
              "Var": [
                "x",
                "VirParam"
              ]
            }
          }
        ]
      }
    }
  ]
}

def extract (j : Json) : (ExpX × VMap) :=
  match ExpX.fromJson? j (.Bool, Std.HashMap.empty) with
  | .ok exp (_, map) => (exp, map)
  | .error e _ =>
    dbg_trace e
    (.Const (.Bool true), .empty)

def f1 := extract ex1
def f2 := extract ex2
def f3 := extract ex3

def f1Decl := Decl.assertion "assert1" f1.2 f1.1
def f2Decl := Decl.assertion "assert2" f2.2 f2.1
def f3Decl := Decl.assertion "assert3" f3.2 f3.1

def synF1 := f1.1.toSyntax
def synF2 := f2.1.toSyntax
def synF3 := f3.1.toSyntax

--#eval f1.1
--#eval f2.2
--#eval f3.2

def preludeString := "import VerusLean.Basic\n\nnamespace VerusLean\n"
def postludeString := "end VerusLean"

/-
def genFromDir (dirPath : String) : IO String := do
  -- For each file in the directory
  let files ← System.FilePath.walkDir dirPath
  let (str, _) ← files.foldlM (init := ("", 1)) (fun (str, counter) entry => do
    -- Get out the filepath in the entry, open it, and run `genFromFile`
    let res ← ExpX.fromFile? entry.toString
    match res with
    | .ok (e, map) =>
      let declsString := map.fold (init := "") (fun str k v => str ++ s!"({k} : {v.toSyntax}) ")
      let str := str ++ e.toTheoremString (name := s!"verus_thm_{counter}") (decls := declsString)
      return (str, counter + 1)
    | .error _ => do
      -- TODO: Error handling?
      let str := str ++ s!"-- The JSON at {entry} failed to generate\n\n"
      return (str, counter)
  )

  return str -/

unsafe def genFromDir' (dirPath : String) : IO String := do
  -- For each file in the directory
  let files ← System.FilePath.walkDir dirPath
  let files := files.insertionSort (fun a b => a.toString < b.toString)
  let str ← files.foldlM (init := "") (fun str entry => do
    let res ← Decls.fromFile? entry.toString
    match res with
    | .ok decls => do
      dbg_trace s!"get here, toFormat is the problem"
      let mut res := str
      for d in decls do
        let fmt ← d.toFormat
        res := res ++ fmt ++ "\n\n"
      return res
      -- return str ++ fmt ++ "\n\n"
    | .error e => do
      dbg_trace e
      let str := str ++ s!"-- The JSON at {entry} failed to generate\n\n"
      return str
  )

  return str

unsafe def main : List String → IO Unit
  | [path] => do
    let res ← ExpX.fromFile? path
    match res with
    | .ok (e, map) =>
      let declsString := map.fold (init := " ") (fun str k _ => str ++ s!"({k} : Bool) ")
      IO.println <| preludeString ++ e.toTheoremString (decls := declsString) ++ postludeString
    | .error e => IO.println e
  | ["dir", path] => do
    -- IO.println "Reading from a directory"
    let res ← genFromDir' path
    IO.println <| preludeString ++ res ++ postludeString
  | [path, toFile] => do
    let res ← ExpX.fromFile? path
    match res with
    | .ok (e, map) =>
      let declsString := map.fold (init := "") (fun str k _ => str ++ s!"({k} : Bool) ")
      IO.FS.writeFile toFile (preludeString ++ e.toTheoremString (decls := declsString) ++ postludeString)
    | .error e => IO.println e
  | ["dir", path, toFile] => do
    -- IO.println "Reading from a directory"
    let res ← genFromDir' path
    IO.FS.writeFile toFile (preludeString ++ res ++ postludeString)
  | _ =>
    IO.println "Wrong number of arguments"

#exit
--#check Elab.Command.liftTermElabM
--#check delab
#check ppCommand
#check ppTerm
#check PPContext
#check Environment

#eval ~~~ (1 : BitVec 32)
/-
structure PPContext where
  env           : Environment
  mctx          : MetavarContext := {}
  lctx          : LocalContext := {}
  opts          : Options := {}
  currNamespace : Name := Name.anonymous
  openDecls     : List OpenDecl := []
-/

#check Lean.liftCommandElabM
#check Elab.TermElabM Term

unsafe def formatter (t : Elab.TermElabM Term) : IO String := do
  let r ← Elab.Command.liftTermElabM t

  let res : Except Exception Format ← Lean.withImportModules
    (imports := #[`Init])
    (opts := Options.empty)
    (trustLevel := 0)
    (fun env => EIO.toIO' <|
      Core.CoreM.run'
        (ctx := {
          fileName := "Example.lean"
          fileMap := default
        })
        (s := {
          env
        })
        (do
          Lean.PrettyPrinter.ppCategory `hello syn
          /-let mut fmt : Format := ""
          let syn ← Lean.liftCommandElabM syn
          for c in syn do
            Lean.liftCommandElabM <| Elab.Command.elabCommandTopLevel c
          for c in syn do
            fmt := fmt ++ .line ++ (
              ← Lean.PrettyPrinter.format (Formatter.categoryFormatter `command) c
            )
          return fmt -/
        )
    )
  match res with
  | .error _ => return "bad syntax"
  | .ok res => return Std.Format.pretty res

#eval formatter synF1



/-

opaque STOP_ON_ERROR : Bool := true

def format (formatter : Formatter) (stx : Syntax) : CoreM Format := do
  trace[PrettyPrinter.format.input] "{Std.format stx}"
  let options ← getOptions
  let table ← Parser.builtinTokenTable.get
  catchInternalId backtrackExceptionId
    (do
      let (_, st) ← (Formatter.concat formatter { table, options }).run { stxTrav := .fromSyntax stx }
      let mut f := st.stack[0]!
      if pp.oneline.get options then
        let mut s := f.pretty' options |>.trim
        let lineEnd := s.find (· == '\n')
        if lineEnd < s.endPos then
          s := s.extract 0 lineEnd ++ " [...]"
        -- TODO: preserve `Format.tag`s?
        f := s
      return .fill f)
    (fun ex => throwError "format: uncaught backtrack exception: {ex.toMessageData}")

unsafe def main (args : List String) : IO Unit := do
  let path := args[0]!
  let resPath := args[1]!
  IO.println s!"Reading file {path}"
  let json_str ← IO.FS.readFile path
  let fns ← do
    let arr ← IO.ofExcept <| (do (← Lean.Json.parse json_str).getArr?)
    arr.filterMapM fun j => do
      match Function.fromJson? j with
      | .ok j => return some j
      | .error e =>
        if STOP_ON_ERROR then
          throw (.userError e)
        else
          IO.println e
          return none
  IO.println s!"Converting functions to Lean syntax"
  let fns' ← Lean.withImportModules
    (imports := #[`Init])
    (opts := Options.empty)
    (trustLevel := 0)
    <| fun env => EIO.toIO' <|
    Lean.Core.CoreM.run'
      (ctx := {
        fileName := "Example.lean"
        fileMap := default
      })
      (s := {
        env
      })
      (fns.filterMapM (fun f => do
        IO.println s!"{f.id.segments}: processing"
        try
          let syn ← Lean.liftCommandElabM (Function.toSyntax f)
          IO.println s!"{f.id.segments}: typechecking"
          for c in syn do
            Lean.liftCommandElabM <| Elab.Command.elabCommandTopLevel c
          IO.println s!"{f.id.segments}: formatting"
          let mut fmt : Format := ""
          for c in syn do
            fmt := fmt ++ .line ++ (
              ← _root_.format (Formatter.categoryFormatter `command) c
            )
          IO.println s!"{f.id.segments}: done"
          return some fmt
        catch exc =>
          IO.println s!"{f.id.segments}: error: {← exc.toMessageData.toString}"
          return none)
      )
  match fns' with
  | .error exc =>
    IO.println (← exc.toMessageData.toString)
  | .ok fns' =>
  IO.println s!"Writing syntax to file {resPath}"
  let formatted : Lean.Format :=
    fns'.foldr (fun x acc => x ++ .line ++ .line ++ acc)
      ""
  IO.FS.writeFile resPath (formatted.pretty)
  IO.println s!"Finished!"

#eval main ["example/example_verus/vir.json", "example/example_verus/Example.lean"]

-/
