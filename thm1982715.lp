require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982715_term_abbrevs;
require open hol-light.thm1982712_spec;
opaque symbol lem1982715 (a : El real) (m : El real) : Prf (= (term0 a m) (term1 a m)) ≔ ∧ₑ₁ (@lem1982712 m (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
