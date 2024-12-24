require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 a2 ≔ (λ y0 : El (type2 a0 a1 a2), ((@lambda a0 a1) (λ y1 : El num, ((@﹩ a0 (finite_sum a1 a2)) y0 y1))));
symbol term4 a0 a1 a2 (x0: El (type2 a0 a1 a2)) ≔ ((λ y0 : El (type2 a0 a1 a2), (= ((@fstcart a0 a1 a2) y0) ((@lambda a0 a1) (λ y1 : El num, ((@﹩ a0 (finite_sum a1 a2)) y0 y1))))) x0);
symbol term1 a0 a1 a2 (x0: El (type2 a0 a1 a2)) ≔ ((λ y0 : El (type2 a0 a1 a2), ((@lambda a0 a1) (λ y1 : El num, ((@﹩ a0 (finite_sum a1 a2)) y0 y1)))) x0);
symbol term3 a0 a1 a2 ≔ (∀ (λ y0 : El (type2 a0 a1 a2), (= ((@fstcart a0 a1 a2) y0) ((@lambda a0 a1) (λ y1 : El num, ((@﹩ a0 (finite_sum a1 a2)) y0 y1))))));
symbol term2 a0 a1 a2 (x0: El (type2 a0 a1 a2)) ≔ ((@lambda a0 a1) (λ y0 : El num, ((@﹩ a0 (finite_sum a1 a2)) x0 y0)));
