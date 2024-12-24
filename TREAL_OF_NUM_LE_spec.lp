require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1327029 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (treal_le (treal_of_num m) (treal_of_num n)) (<= m n))))));
