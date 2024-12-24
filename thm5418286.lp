require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm5418286_term_abbrevs;
require open hol-light.thm5400808_spec;
require open hol-light.thm5404127_spec;
opaque symbol lem5418286 (m : El num) (h1 : Prf (= m (NUMERAL _0))) : Prf (term0 m) ≔ (@lem5404127 m) (@lem5400808 m h1);
