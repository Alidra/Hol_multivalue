require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem89009 : Prf (∀ (λ x : El num, (∀ (λ m : El num, (∀ (λ n : El num, (= (EXP (EXP x m) n) (EXP x (* m n)))))))));
