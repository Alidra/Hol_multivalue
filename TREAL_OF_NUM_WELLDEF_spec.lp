require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1332671 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (= m n) (treal_eq (treal_of_num m) (treal_of_num n)))))));
