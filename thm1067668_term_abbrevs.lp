require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ (λ y0 : El a1, ((@_mk_sum a0 a1) ((λ y1 : El a1, ((@CONSTR (prod a0 a1)) (SUC (NUMERAL _0)) ((@̦‚ a0 a1) ((@ε a0) (λ y2 : El a0, T)) y1) (λ y2 : El num, (@BOTTOM (prod a0 a1))))) y0)));
