require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem178251 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (∀ (λ q : El num, (⇒ (= m (+ n (* q p))) (= (MOD m p) (MOD n p)))))))))));
