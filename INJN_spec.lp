require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1055402 [A] : Prf (∀ (λ m : El num, (= ((@INJN A) m) (λ n : El num, (λ a : El A, (= n m))))));
