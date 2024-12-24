require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 a1 a2 (x0: El (type1475 a0 a1 a2)) ≔ (∀ (λ y0 : El (list a2), (= ((@MAP2 a0 a1 a2) x0 (@NIL a1) y0) (@NIL a0))));
symbol term0 a0 a1 a2 ≔ (∀ (λ y0 : El (type1475 a0 a1 a2), (∀ (λ y1 : El (list a2), (= ((@MAP2 a0 a1 a2) y0 (@NIL a1) y1) (@NIL a0))))));
symbol term1 a0 a1 a2 (x0: El (type1475 a0 a1 a2)) ≔ ((λ y0 : El (type1475 a0 a1 a2), (∀ (λ y1 : El (list a2), (= ((@MAP2 a0 a1 a2) y0 (@NIL a1) y1) (@NIL a0))))) x0);
symbol term3 a0 a1 a2 (x0: El (type1475 a0 a1 a2)) (x1: El (list a2)) ≔ ((λ y0 : El (list a2), (= ((@MAP2 a0 a1 a2) x0 (@NIL a1) y0) (@NIL a0))) x1);
