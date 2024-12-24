require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm20762_term_abbrevs;
require open hol-light.thm20708_spec;
require open hol-light.thm20738_spec;
opaque symbol lem20762 (b : El bool) (a : El bool) (h1 : Prf (= a T)) : Prf (= (∨ a b) (term0 b a)) ≔ EQ_MP (@lem20708 b a h1) (@lem20738 b);
