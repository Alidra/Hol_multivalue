require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem204674 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (EVEN n) (= (ODD (MOD m n)) (ODD m)))))));
