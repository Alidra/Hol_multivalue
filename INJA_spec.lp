require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1055868 [A] : Prf (∀ (λ a : El A, (= ((@INJA A) a) (λ n : El num, (λ b : El A, (= b a))))));
