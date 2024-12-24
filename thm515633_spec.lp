require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem515633 : Prf (∧ (∀ (λ m : El num, (= (EXP m _0) (BIT1 _0)))) (∀ (λ m : El num, (∀ (λ n : El num, (= (EXP m (SUC n)) (* m (EXP m n))))))));
