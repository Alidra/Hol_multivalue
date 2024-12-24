require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem528184 (n : El num) : Prf (= ((λ n' : El num, (= (SUC (BIT1 n')) (BIT0 (SUC n')))) n) (= (SUC (BIT1 n)) (BIT0 (SUC n))));
