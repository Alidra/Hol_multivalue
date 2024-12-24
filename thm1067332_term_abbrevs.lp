require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ (λ y0 : El a0, ((@CONSTR (prod a0 a1)) (NUMERAL _0) ((@̦‚ a0 a1) y0 ((@ε a1) (λ y1 : El a1, T))) (λ y1 : El num, (@BOTTOM (prod a0 a1)))));
symbol term2 a0 a1 (x0: El (type1431 a0 a1)) ≔ (λ y0 : El a0, ((@_mk_sum a0 a1) (x0 y0)));
symbol term1 a0 a1 ≔ (λ y0 : El a0, ((@_mk_sum a0 a1) ((λ y1 : El a0, ((@CONSTR (prod a0 a1)) (NUMERAL _0) ((@̦‚ a0 a1) y1 ((@ε a1) (λ y2 : El a1, T))) (λ y2 : El num, (@BOTTOM (prod a0 a1))))) y0)));
