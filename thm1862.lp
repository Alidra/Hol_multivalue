require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1862_term_abbrevs;
require open hol-light.REFL_CLAUSE_spec;
opaque symbol lem1862 [A] (x : El A) : Prf (term0 A x) ≔ (@lem317 A) x;
