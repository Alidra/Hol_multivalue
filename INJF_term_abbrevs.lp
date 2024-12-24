require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term4 a0 (x0: El (type1600 a0)) ≔ ((λ y0 : El (type1600 a0), (= ((@INJF a0) y0) (λ y1 : El num, (y0 (NUMFST y1) (NUMSND y1))))) x0);
symbol term1 a0 (x0: El (type1600 a0)) ≔ ((λ y0 : El (type1600 a0), (λ y1 : El num, (y0 (NUMFST y1) (NUMSND y1)))) x0);
symbol term0 a0 ≔ (λ y0 : El (type1600 a0), (λ y1 : El num, (y0 (NUMFST y1) (NUMSND y1))));
symbol term3 a0 ≔ (∀ (λ y0 : El (type1600 a0), (= ((@INJF a0) y0) (λ y1 : El num, (y0 (NUMFST y1) (NUMSND y1))))));
symbol term2 a0 (x0: El (type1600 a0)) ≔ (λ y0 : El num, (x0 (NUMFST y0) (NUMSND y0)));
