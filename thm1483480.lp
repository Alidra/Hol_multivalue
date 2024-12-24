require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483480_term_abbrevs;
require open hol-light.thm1483477_spec;
opaque symbol lem1483480 (a : El real) (c : El real) (b : El real) (d : El real) : Prf (= (term0 a b c d) (term0 a c b d)) ≔ ∧ₑ₁ (@lem1483477 b a c d (@el num) (@el real) (@el real) (@el real) (@el num));
