require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1032066_term_abbrevs;
require open hol-light.thm1032063_spec;
opaque symbol lem1032066 (a : El num) : Prf (= (term0 a) (NUMERAL _0)) ≔ ∧ₑ₁ (@lem1032063 (@el num) (@el num) (@el num) (@el num) (@el num) a (@el num) (@el num) (@el num) (@el num) (@el num) (@el num) (@el num));
