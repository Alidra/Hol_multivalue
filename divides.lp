require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.divides_term_abbrevs;
require open hol-light.thm3073436_spec;
require open hol-light.thm3074596_spec;
opaque symbol lem3074597 (b : El num) (a : El num) : Prf (= (num_divides a b) (term0 b a)) ≔ EQ_MP (@lem3073436 b a) (@lem3074596 b a);
