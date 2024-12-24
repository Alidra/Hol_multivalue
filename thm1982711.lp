require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982711_term_abbrevs;
require open hol-light.thm1982708_spec;
opaque symbol lem1982711 (a : El real) (b : El real) (m : El real) : Prf (= (term0 a b m) (term1 a b m)) ≔ ∧ₑ₁ (@lem1982708 m (@el real) (@el real) (@el real) (@el real) b a (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
