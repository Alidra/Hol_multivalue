require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem522119 (m : El num) : Prf ((λ m' : El num, (= (SUC m') (+ m' (NUMERAL (BIT1 _0))))) m);
