require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982721_term_abbrevs;
require open hol-light.thm1982718_spec;
opaque symbol lem1982721 (a : El real) : Prf (= (term0 a) a) ≔ ∧ₑ₁ (@lem1982718 (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
