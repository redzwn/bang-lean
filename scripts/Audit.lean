import Bang
open Lean Elab Command

/-- `#audit_axioms` walks over every declaration defined in a module of this project and fails
unless each one depends on no axioms other than `propext`, `Classical.choice`, `Quot.sound`. -/
elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut theorems := 0
  let mut bad : Array (Name × Name) := #[]
  for (c, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod.getRoot == `Bang do continue
    let axs ← liftCoreM (collectAxioms c)
    checked := checked + 1
    if info matches .thmInfo _ then theorems := theorems + 1
    for a in axs do
      unless allowed.contains a do bad := bad.push (c, a)
  if checked == 0 then throwError "audit: no declarations found (nothing was checked)"
  unless bad.isEmpty do
    throwError "audit: non-standard axioms used: {bad}"
  logInfo m!"audit: {checked} declarations ({theorems} theorems) in the Bang modules; every one depends only on axioms among [propext, Classical.choice, Quot.sound]"

#audit_axioms
#print axioms Bang.dist_eq_of_volume_faceOpposite_eq
#print axioms Bang.volume_faceOpposite_eq_of_dist_eq
#print axioms Bang.volume_faceOpposite_eq_iff_dist_eq
#print axioms Bang.sum_infDist_facetSpan_const_iff_dist_eq
#print axioms Bang.sum_infDist_facetSpan_eq_height
#print axioms Bang.Examples.volume_faceOpposite
#print axioms Bang.Examples.dist_eq_of_bang
#print axioms Bang.Examples.sum_infDist_eq
