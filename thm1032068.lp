require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1032068_term_abbrevs;
require open hol-light.thm1032065_spec;
opaque symbol lem1032068 (a : El num) : Prf (= (term0 a) (NUMERAL _0)) ≔ ∧ₑ₁ (@lem1032065 (@el num) (@el num) (@el num) (@el num) (@el num) a (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num));
