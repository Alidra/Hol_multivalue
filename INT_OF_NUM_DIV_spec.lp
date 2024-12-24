require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2538105 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (div (int_of_num m) (int_of_num n)) (int_of_num (DIV m n)))))));
