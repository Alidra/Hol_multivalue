require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5371143 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (<= m (SUC n)) (= (… m (SUC n)) ((@INSERT num) (SUC n) (… m n))))))));
