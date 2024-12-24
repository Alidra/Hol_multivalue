require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 a1 (x0: El (list a0)) ≔ ((λ y0 : El (list a0), ((@lambda a0 a1) (λ y1 : El num, ((@EL a0) (- y1 (NUMERAL (BIT1 _0))) y0)))) x0);
symbol term2 a0 a1 (x0: El (list a0)) ≔ ((@lambda a0 a1) (λ y0 : El num, ((@EL a0) (- y0 (NUMERAL (BIT1 _0))) x0)));
symbol term0 a0 a1 ≔ (λ y0 : El (list a0), ((@lambda a0 a1) (λ y1 : El num, ((@EL a0) (- y1 (NUMERAL (BIT1 _0))) y0))));
symbol term3 a0 a1 ≔ (∀ (λ y0 : El (list a0), (= ((@vector a0 a1) y0) ((@lambda a0 a1) (λ y1 : El num, ((@EL a0) (- y1 (NUMERAL (BIT1 _0))) y0))))));
symbol term4 a0 a1 (x0: El (list a0)) ≔ ((λ y0 : El (list a0), (= ((@vector a0 a1) y0) ((@lambda a0 a1) (λ y1 : El num, ((@EL a0) (- y1 (NUMERAL (BIT1 _0))) y0))))) x0);
