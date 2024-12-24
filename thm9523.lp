require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm9523_term_abbrevs;
require open hol-light.SELECT_REFL_spec;
opaque symbol lem9523 [A] (x : El A) : Prf (term0 A x) ≔ (@lem9442 A) x;
