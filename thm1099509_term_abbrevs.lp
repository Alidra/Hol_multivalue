require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El a0, (= ((@REPLICATE a0) (SUC y0) y1) ((@CONS a0) y1 ((@REPLICATE a0) y0 y1)))))));
