require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ (∀ (λ y0 : El a0, (∀ (λ y1 : El (list a0), (∀ (λ y2 : El (list a0), (= ((@APPEND a0) ((@CONS a0) y0 y1) y2) ((@CONS a0) y0 ((@APPEND a0) y1 y2)))))))));
symbol term2 a0 ≔ (∧ (∀ (λ y0 : El (list a0), (= ((@APPEND a0) (@NIL a0) y0) y0))) (∀ (λ y0 : El a0, (∀ (λ y1 : El (list a0), (∀ (λ y2 : El (list a0), (= ((@APPEND a0) ((@CONS a0) y0 y1) y2) ((@CONS a0) y0 ((@APPEND a0) y1 y2))))))))));
symbol term1 a0 ≔ (∀ (λ y0 : El (list a0), (= ((@APPEND a0) (@NIL a0) y0) y0)));
