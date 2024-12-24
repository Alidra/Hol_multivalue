require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 (x0: El (list a0)) ≔ (∀ (λ y0 : El a0, (= ((@REVERSE a0) ((@CONS a0) y0 x0)) ((@APPEND a0) ((@REVERSE a0) x0) ((@CONS a0) y0 (@NIL a0))))));
symbol term2 a0 (x0: El (list a0)) (x1: El a0) ≔ ((λ y0 : El a0, (= ((@REVERSE a0) ((@CONS a0) y0 x0)) ((@APPEND a0) ((@REVERSE a0) x0) ((@CONS a0) y0 (@NIL a0))))) x1);
symbol term0 a0 (x0: El (list a0)) ≔ ((λ y0 : El (list a0), (∀ (λ y1 : El a0, (= ((@REVERSE a0) ((@CONS a0) y1 y0)) ((@APPEND a0) ((@REVERSE a0) y0) ((@CONS a0) y1 (@NIL a0))))))) x0);
