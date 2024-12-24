require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ (λ y0 : El a0, (λ y1 : El (list a0), ((@_mk_list a0) ((λ y2 : El a0, (λ y3 : El (recspace a0), ((@CONSTR a0) (SUC (NUMERAL _0)) y2 ((@FCONS (recspace a0)) y3 (λ y4 : El num, (@BOTTOM a0)))))) y0 ((@_dest_list a0) y1)))));
