require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483478_term_abbrevs;
require open hol-light.thm1483475_spec;
opaque symbol lem1483478 (rx : El real) (lx : El real) (ry : El real) : Prf (= (term0 lx rx ry) (term0 rx lx ry)) ≔ ∧ₑ₁ (@lem1483475 rx lx ry (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
