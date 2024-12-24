require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982723_term_abbrevs;
require open hol-light.thm1982720_spec;
opaque symbol lem1982723 (a : El real) : Prf (= (term0 a) a) ≔ ∧ₑ₁ (@lem1982720 (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
