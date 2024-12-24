require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm21596_term_abbrevs;
require open hol-light.thm21529_spec;
require open hol-light.thm21568_spec;
opaque symbol lem21596 (b : El bool) (a : El bool) (h1 : Prf (= a T)) : Prf (term0 b a) ≔ EQ_MP (@lem21529 b a h1) (@lem21568 b);
