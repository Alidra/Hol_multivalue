require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2416555_term_abbrevs;
require open hol-light.thm2416552_spec;
opaque symbol lem2416555 (a : El int) (c : El int) (b : El int) (d : El int) : Prf (= (term0 a b c d) (term0 a c b d)) ≔ ∧ₑ₁ (@lem2416552 b a c d (@el num) (@el int) (@el int) (@el int) (@el num));
