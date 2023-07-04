import Lake
open Lake DSL

def leanArgs := #["-Dlinter.unusedVariables=false", "-DautoImplicit=false"]

package GroundZero { moreServerArgs := leanArgs, moreLeanArgs := leanArgs }

@[default_target]
lean_lib GroundZero
