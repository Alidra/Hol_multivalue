require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El (recspace a0)) ≔ ((λ y0 : El (recspace a0), (∀ (λ y1 : El (type1338 a0), (⇒ (∀ (λ y2 : El (recspace a0), (⇒ (∨ (= y2 ((@CONSTR a0) (NUMERAL _0) ((@ε a0) (λ y3 : El a0, T)) (λ y3 : El num, (@BOTTOM a0)))) (∃ (λ y3 : El a0, (= y2 ((λ y4 : El a0, ((@CONSTR a0) (SUC (NUMERAL _0)) y4 (λ y5 : El num, (@BOTTOM a0)))) y3))))) (y1 y2)))) (y1 y0))))) x0);
symbol term1 a0 (x0: El (recspace a0)) ≔ ((@_dest_option a0) ((@_mk_option a0) x0));
