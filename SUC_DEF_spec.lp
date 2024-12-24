require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem71593 : Prf (∀ (λ n : El num, (= (SUC n) (mk_num (IND_SUC (dest_num n))))));
