/-
Copyright (c) 2026 iVAE formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: iVAE formalization contributors
-/
import Ivae
import Lean.Util.CollectAxioms

/-!
# Check the foundational dependencies of the almost-everywhere proof

Run `lake env lean scripts/CheckAxioms.lean` after `lake build`.
Reject any axiom beyond Lean's three usual foundational axioms.
-/

open Lean Elab Command

run_cmd do
  let targets : Array Name := #[
    ``IVAE.correctedTheorem1_stepI_II_III,
    ``IVAE.correctedTheorem1_all_conditional_laws,
    ``IVAE.affineWitness_bijective,
    ``IVAE.aeAffineNondegenerate_iff_dotProduct,
    ``IVAE.simAAE_equivalence]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{target} depends on an unexpected axiom: {axiomName}"
    logInfo m!"{target}: {axioms.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"
