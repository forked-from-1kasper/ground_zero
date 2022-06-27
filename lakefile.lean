import Lake
open Lake DSL

package GroundZero {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[defaultTarget]
lean_lib GroundZero
