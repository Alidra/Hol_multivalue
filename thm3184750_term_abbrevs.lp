require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ (∀ (λ y0 : El (type919 a0), (∀ (λ y1 : El a0, (= ((@IN a0) y1 ((@GSPEC a0) (λ y2 : El a0, (y0 ((@SETSPEC a0) y2))))) (y0 (λ y2 : El bool, (λ y3 : El a0, (∧ y2 (= y1 y3))))))))));
