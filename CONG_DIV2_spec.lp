require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3070924 : Prf (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ m : El num, (∀ (λ n : El num, (⇒ ((@== num) a b (num_mod (* m n))) ((@== num) (DIV a m) (DIV b m) (num_mod n)))))))))));
