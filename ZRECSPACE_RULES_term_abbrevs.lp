require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ (∧ ((@ZRECSPACE a0) (@ZBOT a0)) (∀ (λ y0 : El num, (∀ (λ y1 : El a0, (∀ (λ y2 : El (type1600 a0), (⇒ (∀ (λ y3 : El num, ((@ZRECSPACE a0) (y2 y3)))) ((@ZRECSPACE a0) ((@ZCONSTR a0) y0 y1 y2))))))))));
