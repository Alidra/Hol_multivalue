require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem515681 (m : El num) (n : El num) : Prf ((λ n' : El num, (= (EXP m (SUC n')) (* m (EXP m n')))) n);
