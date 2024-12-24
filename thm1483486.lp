require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483486_term_abbrevs;
require open hol-light.thm1483483_spec;
opaque symbol lem1483486 (a : El real) (c : El real) (b : El real) : Prf (= (term0 a b c) (term0 a c b)) ≔ ∧ₑ₁ (@lem1483483 b a c (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
