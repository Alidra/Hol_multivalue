require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 (x0: El (type1143 a0)) ≔ (⇒ (∧ (x0 (@NIL a0)) (∀ (λ y0 : El a0, (∀ (λ y1 : El (list a0), (⇒ (x0 y1) (x0 ((@CONS a0) y0 y1)))))))) (∀ (λ y0 : El (list a0), (x0 y0))));
symbol term0 a0 (x0: El (type1143 a0)) ≔ ((λ y0 : El (type1143 a0), (⇒ (∧ (y0 (@NIL a0)) (∀ (λ y1 : El a0, (∀ (λ y2 : El (list a0), (⇒ (y0 y2) (y0 ((@CONS a0) y1 y2)))))))) (∀ (λ y1 : El (list a0), (y0 y1))))) x0);
