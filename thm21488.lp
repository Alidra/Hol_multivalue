require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm21488_term_abbrevs;
require open hol-light.thm21420_spec;
require open hol-light.thm21460_spec;
opaque symbol lem21488 (b : El bool) (a : El bool) (h1 : Prf (= a T)) : Prf (= (⇒ a b) (term0 a b)) ≔ EQ_MP (@lem21420 b a h1) (@lem21460 b);
