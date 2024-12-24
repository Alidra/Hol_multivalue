require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982735_term_abbrevs;
require open hol-light.thm1982732_spec;
opaque symbol lem1982735 (a : El real) : Prf (= (term0 a) a) ≔ ∧ₑ₁ (@lem1982732 (@el real) (@el real) (@el real) (@el real) (@el real) a (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
