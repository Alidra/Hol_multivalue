require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem204570 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (EVEN n) (= (EVEN (MOD m n)) (EVEN m)))))));
