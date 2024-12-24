require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1327157 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (treal_eq (treal_add (treal_of_num m) (treal_of_num n)) (treal_of_num (+ m n)))))));
