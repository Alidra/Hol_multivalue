require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5443756 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (∀ (λ q : El num, (= ((@INTER num) (… m n) (… p q)) (… (MAX m p) (MIN n q)))))))))));
