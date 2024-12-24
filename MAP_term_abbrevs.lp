require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 a1 ≔ (∧ (∀ (λ y0 : El (fun a0 a1), (= ((@MAP a0 a1) y0 (@NIL a0)) (@NIL a1)))) (∀ (λ y0 : El (fun a0 a1), (∀ (λ y1 : El a0, (∀ (λ y2 : El (list a0), (= ((@MAP a0 a1) y0 ((@CONS a0) y1 y2)) ((@CONS a1) (y0 y1) ((@MAP a0 a1) y0 y2))))))))));
symbol term1 a0 a1 ≔ (∀ (λ y0 : El (fun a0 a1), (= ((@MAP a0 a1) y0 (@NIL a0)) (@NIL a1))));
symbol term0 a0 a1 ≔ (∀ (λ y0 : El (fun a0 a1), (∀ (λ y1 : El a0, (∀ (λ y2 : El (list a0), (= ((@MAP a0 a1) y0 ((@CONS a0) y1 y2)) ((@CONS a1) (y0 y1) ((@MAP a0 a1) y0 y2)))))))));
