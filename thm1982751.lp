require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982751_term_abbrevs;
require open hol-light.thm1982748_spec;
opaque symbol lem1982751 (rx : El real) (lx : El real) (ry : El real) : Prf (= (term0 lx rx ry) (term0 rx lx ry)) ≔ ∧ₑ₁ (@lem1982748 rx lx ry (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
