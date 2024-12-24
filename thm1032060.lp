require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1032060_term_abbrevs;
require open hol-light.thm1032057_spec;
opaque symbol lem1032060 (a : El num) : Prf (= (term0 a) a) ≔ ∧ₑ₁ (@lem1032057 (@el num) (@el num) (@el num) (@el num) (@el num) a (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num));
