require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 ≔ ((@COND num) ((@FINITE a0) (@UNIV a0)) ((@CARD a0) (@UNIV a0)) (NUMERAL (BIT1 _0)));
symbol term3 a0 ≔ (∀ (λ y0 : El (fun a0 bool), (= ((@dimindex a0) y0) ((@COND num) ((@FINITE a0) (@UNIV a0)) ((@CARD a0) (@UNIV a0)) (NUMERAL (BIT1 _0))))));
symbol term4 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (= ((@dimindex a0) y0) ((@COND num) ((@FINITE a0) (@UNIV a0)) ((@CARD a0) (@UNIV a0)) (NUMERAL (BIT1 _0))))) x0);
symbol term0 a0 ≔ (λ y0 : El (fun a0 bool), ((@COND num) ((@FINITE a0) (@UNIV a0)) ((@CARD a0) (@UNIV a0)) (NUMERAL (BIT1 _0))));
symbol term1 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), ((@COND num) ((@FINITE a0) (@UNIV a0)) ((@CARD a0) (@UNIV a0)) (NUMERAL (BIT1 _0)))) x0);
