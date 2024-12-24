require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El int) (x1: El int) ≔ (int_mul (int_add x0 (int_of_num (NUMERAL (BIT1 _0)))) x1);
symbol term0 (x0: El int) (x1: El int) ≔ (int_add x1 (int_mul x0 x1));
