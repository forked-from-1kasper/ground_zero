import Lake
open Lake DSL

package GroundZero {
  defaultFacet := PackageFacet.oleans
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}
