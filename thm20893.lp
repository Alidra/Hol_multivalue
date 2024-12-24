require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm20893_term_abbrevs;
require open hol-light.thm20815_spec;
require open hol-light.thm20862_spec;
opaque symbol lem20893 (b : El bool) (a : El bool) (h1 : Prf (= a T)) : Prf (= (term0 a b) (term1 a b)) ≔ EQ_MP (@lem20815 b a h1) (@lem20862 b);
