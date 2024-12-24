require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3211730_term_abbrevs;
require open hol-light.thm82_spec;
opaque symbol lem3211730 [A] (x : El A) : Prf (term0 A x) ≔ (@lem82 ((@IN A) x (@EMPTY A)));
