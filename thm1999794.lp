require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1999794_term_abbrevs;
require open hol-light.thm1386578_spec;
opaque symbol lem1999794 (x : El real) (y : El real) : Prf (term0 x y) ≔ (@lem1386578 (= (real_lt x y) (term1 x y)));
