require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem522190 (m : El num) (n : El num) : Prf (= ((λ n' : El num, (= (- (SUC m) (SUC n')) (- m n'))) n) (= (- (SUC m) (SUC n)) (- m n)));
