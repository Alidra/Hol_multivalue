require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 a1 (x0: El a0) ≔ (∀ (λ y0 : El (list a0), (∀ (λ y1 : El (list a1), (= ((@ZIP a0 a1) ((@CONS a0) x0 y0) y1) ((@CONS (prod a0 a1)) ((@̦‚ a0 a1) x0 ((@HD a1) y1)) ((@ZIP a0 a1) y0 ((@TL a1) y1))))))));
symbol term3 a0 a1 (x0: El a0) (x1: El (list a0)) ≔ (∀ (λ y0 : El (list a1), (= ((@ZIP a0 a1) ((@CONS a0) x0 x1) y0) ((@CONS (prod a0 a1)) ((@̦‚ a0 a1) x0 ((@HD a1) y0)) ((@ZIP a0 a1) x1 ((@TL a1) y0))))));
symbol term0 a0 a1 (x0: El a0) ≔ ((λ y0 : El a0, (∀ (λ y1 : El (list a0), (∀ (λ y2 : El (list a1), (= ((@ZIP a0 a1) ((@CONS a0) y0 y1) y2) ((@CONS (prod a0 a1)) ((@̦‚ a0 a1) y0 ((@HD a1) y2)) ((@ZIP a0 a1) y1 ((@TL a1) y2))))))))) x0);
symbol term4 a0 a1 (x0: El a0) (x1: El (list a0)) (x2: El (list a1)) ≔ ((λ y0 : El (list a1), (= ((@ZIP a0 a1) ((@CONS a0) x0 x1) y0) ((@CONS (prod a0 a1)) ((@̦‚ a0 a1) x0 ((@HD a1) y0)) ((@ZIP a0 a1) x1 ((@TL a1) y0))))) x2);
symbol term2 a0 a1 (x0: El a0) (x1: El (list a0)) ≔ ((λ y0 : El (list a0), (∀ (λ y1 : El (list a1), (= ((@ZIP a0 a1) ((@CONS a0) x0 y0) y1) ((@CONS (prod a0 a1)) ((@̦‚ a0 a1) x0 ((@HD a1) y1)) ((@ZIP a0 a1) y0 ((@TL a1) y1))))))) x1);
