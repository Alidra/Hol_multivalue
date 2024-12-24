require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem513549 : Prf (∀ (λ n : El num, (= (PRE (+ n n)) ((@COND num) (= n _0) _0 (SUC (+ (PRE n) (PRE n)))))));
