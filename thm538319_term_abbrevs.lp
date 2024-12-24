require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) (x1: El num) ≔ (+ (BIT0 x0) (BIT0 x1));
symbol term3 ≔ (BIT0 (+ (BIT0 (BIT1 _0)) (BIT1 _0)));
symbol term2 ≔ (+ (BIT0 (BIT0 (BIT1 _0))) (BIT0 (BIT1 _0)));
symbol term4 ≔ (BIT0 (BIT1 _0));
symbol term1 (x0: El num) (x1: El num) ≔ (BIT0 (+ x0 x1));
