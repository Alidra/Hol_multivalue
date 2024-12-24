require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term3 a0 (x0: El (type686 a0)) ≔ ((λ y0 : El (type686 a0), (= ((@ARBITRARY a0) y0) T)) x0);
symbol term2 a0 ≔ (∀ (λ y0 : El (type686 a0), (= ((@ARBITRARY a0) y0) T)));
symbol term1 a0 (x0: El (type686 a0)) ≔ ((λ y0 : El (type686 a0), T) x0);
symbol term0 a0 ≔ (λ y0 : El (type686 a0), T);
