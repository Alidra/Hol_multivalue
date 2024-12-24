require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982779_term_abbrevs;
require open hol-light.thm1982776_spec;
opaque symbol lem1982779 (x : El real) : Prf (= (term0 x) x) ≔ ∧ₑ₁ (@lem1982776 (@el real) (@el real) x (@el num));
