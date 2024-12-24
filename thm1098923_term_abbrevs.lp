require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 (x0: El a0) ≔ (∀ (λ y0 : El (list a0), (= ((@BUTLAST a0) ((@CONS a0) x0 y0)) ((@COND (list a0)) (= y0 (@NIL a0)) (@NIL a0) ((@CONS a0) x0 ((@BUTLAST a0) y0))))));
symbol term0 a0 (x0: El a0) ≔ ((λ y0 : El a0, (∀ (λ y1 : El (list a0), (= ((@BUTLAST a0) ((@CONS a0) y0 y1)) ((@COND (list a0)) (= y1 (@NIL a0)) (@NIL a0) ((@CONS a0) y0 ((@BUTLAST a0) y1))))))) x0);
symbol term2 a0 (x0: El a0) (x1: El (list a0)) ≔ ((λ y0 : El (list a0), (= ((@BUTLAST a0) ((@CONS a0) x0 y0)) ((@COND (list a0)) (= y0 (@NIL a0)) (@NIL a0) ((@CONS a0) x0 ((@BUTLAST a0) y0))))) x1);
