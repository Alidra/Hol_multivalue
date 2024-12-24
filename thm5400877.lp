require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm5400877_term_abbrevs;
opaque symbol lem5400877 (m : El num) (n : El num) (h1 : Prf (term0 m n)) : Prf (term0 m n) ≔ h1;
