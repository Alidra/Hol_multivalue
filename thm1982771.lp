require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982771_term_abbrevs;
require open hol-light.thm1982768_spec;
opaque symbol lem1982771 (x : El real) : Prf (= (real_mul x x) (term0 x)) ≔ ∧ₑ₁ (@lem1982768 (@el num) (@el real) (@el real) x (@el num));
