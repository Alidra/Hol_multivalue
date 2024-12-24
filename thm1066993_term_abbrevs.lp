require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ (λ y0 : El a0, ((@CONSTR (prod a0 a1)) (NUMERAL _0) ((@̦‚ a0 a1) y0 ((@ε a1) (λ y1 : El a1, T))) (λ y1 : El num, (@BOTTOM (prod a0 a1)))));
symbol term2 a0 a1 (x0: El (type1431 a0 a1)) (x1: El (type1479 a0 a1)) ≔ (λ y0 : El (type1677 a0 a1), (∀ (λ y1 : El (type1333 a0 a1), (⇒ (∀ (λ y2 : El (type1677 a0 a1), (⇒ (∨ (∃ (λ y3 : El a0, (= y2 (x0 y3)))) (∃ (λ y3 : El a1, (= y2 (x1 y3))))) (y1 y2)))) (y1 y0)))));
symbol term1 a0 a1 ≔ (λ y0 : El a1, ((@CONSTR (prod a0 a1)) (SUC (NUMERAL _0)) ((@̦‚ a0 a1) ((@ε a0) (λ y1 : El a0, T)) y0) (λ y1 : El num, (@BOTTOM (prod a0 a1)))));
symbol term3 a0 a1 (x0: El (type1677 a0 a1)) ≔ ((λ y0 : El (type1677 a0 a1), (∀ (λ y1 : El (type1333 a0 a1), (⇒ (∀ (λ y2 : El (type1677 a0 a1), (⇒ (∨ (∃ (λ y3 : El a0, (= y2 ((λ y4 : El a0, ((@CONSTR (prod a0 a1)) (NUMERAL _0) ((@̦‚ a0 a1) y4 ((@ε a1) (λ y5 : El a1, T))) (λ y5 : El num, (@BOTTOM (prod a0 a1))))) y3)))) (∃ (λ y3 : El a1, (= y2 ((λ y4 : El a1, ((@CONSTR (prod a0 a1)) (SUC (NUMERAL _0)) ((@̦‚ a0 a1) ((@ε a0) (λ y5 : El a0, T)) y4) (λ y5 : El num, (@BOTTOM (prod a0 a1))))) y3))))) (y1 y2)))) (y1 y0))))) x0);
