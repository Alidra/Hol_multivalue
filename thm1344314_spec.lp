require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1344314 (x : El real) : Prf (= ((λ x' : El real, (∀ (λ n : El num, (= (real_pow x' (SUC n)) (real_mul x' (real_pow x' n)))))) x) (∀ (λ n : El num, (= (real_pow x (SUC n)) (real_mul x (real_pow x n))))));
