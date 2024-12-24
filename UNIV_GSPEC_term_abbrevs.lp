require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ ((@GSPEC a0) (λ y0 : El a0, (∃ (λ y1 : El a0, ((@SETSPEC a0) y0 T y1)))));
