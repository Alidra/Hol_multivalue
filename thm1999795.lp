require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1999795_term_abbrevs;
require open hol-light.thm1999793_spec;
require open hol-light.thm1999794_spec;
opaque symbol lem1999795 (x : El real) (y : El real) : Prf (= (real_lt x y) (term0 x y)) ≔ (@lem1999794 x y) (@lem1999793 x y);
