require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 (x0: El (fun num a0)) ≔ (∀ (λ y0 : El num, (= ((@list_of_seq a0) x0 (SUC y0)) ((@APPEND a0) ((@list_of_seq a0) x0 y0) ((@CONS a0) (x0 y0) (@NIL a0))))));
symbol term2 a0 (x0: El (fun num a0)) (x1: El num) ≔ ((λ y0 : El num, (= ((@list_of_seq a0) x0 (SUC y0)) ((@APPEND a0) ((@list_of_seq a0) x0 y0) ((@CONS a0) (x0 y0) (@NIL a0))))) x1);
symbol term0 a0 (x0: El (fun num a0)) ≔ ((λ y0 : El (fun num a0), (∀ (λ y1 : El num, (= ((@list_of_seq a0) y0 (SUC y1)) ((@APPEND a0) ((@list_of_seq a0) y0 y1) ((@CONS a0) (y0 y1) (@NIL a0))))))) x0);
