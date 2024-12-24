require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1318990 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (hreal_mul (hreal_of_num m) (hreal_of_num n)) (hreal_of_num (* m n)))))));
