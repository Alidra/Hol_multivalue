require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2299877_term_abbrevs;
opaque symbol lem2299877 (x : El int) (n : El num) : Prf (= (term0 x n) (= (term1 x n) (term2 x n))) ≔ REFL (term0 x n);
