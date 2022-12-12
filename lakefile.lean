import Lake
open Lake DSL

package GroundZero {
  moreLeanArgs := #["-Dlinter.unusedVariables=false",
                    "-DautoImplicit=false"]
}

@[default_target]
lean_lib GroundZero
