require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982729_term_abbrevs;
require open hol-light.thm1982726_spec;
opaque symbol lem1982729 (a : El real) : Prf (= (term0 a) term1) ≔ ∧ₑ₁ (@lem1982726 (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
