import TwoBlock

/-!
Prints the statement and the axioms of each main result. Run from this folder, after `lake build`:

    lake env lean Check.lean

Every result should depend only on Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). The cited bounds enter as hypotheses (`EllisonBound`, `VerifiedBelow`), never as axioms,
and no proof uses `sorry`.
-/

open TwoBlock

-- Section 1
#print axioms c_append
#print axioms M_append
#print axioms follows_iterate
#print axioms IsCycle.eq
#print axioms IsCycle.rotate

-- Section 2
#check @two_block_identities
#print axioms two_block_identities
#check @two_block_dvd
#print axioms two_block_dvd
#print axioms two_block_dvd_of_unimodular

-- Section 3
#check @two_block
#print axioms two_block
#print axioms two_block_rev
#check @any_pair
#print axioms any_pair

-- Section 4
#print axioms D_append_left
#print axioms D_append_right
#print axioms D_root
#print axioms TreePair.unimodular
#print axioms TreePair.det
#print axioms exists_onPath
#check @farey_pair
#print axioms farey_pair
#check @depth_one
#print axioms depth_one

-- Section 5
#print axioms spell_weights
#print axioms spell_dvd
#check @same_side
#print axioms same_side

-- Section 7
#check @stretch_dvd
#print axioms stretch_dvd
#print axioms stretch_exact
#print axioms stretch_exact_dvd
#check @cycle_repeat
#print axioms cycle_repeat
#print axioms cycle_product
#check @repeat_in_orbit_bound
#print axioms repeat_in_orbit
#print axioms repeat_in_orbit_bound

-- Section 6
#check @bracket_X
#print axioms bracket_X
#check @bracket_Y
#print axioms bracket_Y
#check @two_brackets
#print axioms two_brackets
#check @s_alternations
#print axioms s_alternations
#check @s_alternations_laurent
#print axioms s_alternations_laurent
#check @s_alternations_rhin
#print axioms s_alternations_rhin
#check @s_alternations_excluded
#print axioms s_alternations_excluded
#check @two_alternations
#print axioms two_alternations
#check @two_alternations_path
#print axioms two_alternations_path
#check @OnPath.rates_gt
#print axioms OnPath.rates_gt
#print axioms pathK_lt_left
#print axioms pathK_lt_right
#check @deep_pairs
#print axioms deep_pairs
#print axioms deep_check

-- Section 7: Theorem 7.2
#check @periodic_stretch
#print axioms periodic_stretch
#check @periodic_stretch_rhin
#print axioms periodic_stretch_rhin
#print axioms verifiedBelow_ten
#print axioms laurent_root
#print axioms eliahou_check
