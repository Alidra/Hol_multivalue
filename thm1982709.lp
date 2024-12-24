require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982709_term_abbrevs;
require open hol-light.thm1982707_spec;
opaque symbol lem1982709 (x : El real) : Prf (= (term0 x) x) ≔ ∧ₑ₁ (@lem1982707 (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) x (@el num));
