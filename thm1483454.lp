require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483454_term_abbrevs;
require open hol-light.thm1483451_spec;
opaque symbol lem1483454 (a : El real) (b : El real) (c : El real) : Prf (= (term0 a b c) (term1 a b c)) ≔ ∧ₑ₁ (@lem1483451 (@el real) (@el real) (@el real) (@el real) b a c (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
