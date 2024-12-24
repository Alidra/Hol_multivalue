require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm5418290_term_abbrevs;
require open hol-light.thm5400957_spec;
require open hol-light.thm5418286_spec;
opaque symbol lem5418290 (m : El num) (h1 : Prf (= m (NUMERAL _0))) : Prf (term0 m) ≔ EQ_MP (@lem5400957 m) (@lem5418286 m h1);
